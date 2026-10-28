# CLAUDE.md

wchar_t 専用のバックトラック型正規表現エンジン。本体は `uka_regexp.h` + `uka_regexp.cpp` の 2 ファイルだけ（対応構文の仕様書と入門は README.md、C++ の使い方・ビルド・テストは DEVELOPERS.md）。
**方針: PCRE2（Perl 互換）に近づける。** 迷ったら PCRE2 の挙動に合わせ、意図的な差異は README の「PCRE2 との関係と意図的な違い」の表に載せる。構文や挙動を変えたら README の仕様書（と、入門の例に影響するならそちらも）、API を変えたら DEVELOPERS.md を更新する。

## 守ること
- VC6 / 古い GCC でも通る C++98 に限る: STL・C++11・複雑なテンプレート不可、`for (int i…)` で変数を宣言しない（VC6 はスコープが漏れる）、`snprintf` や `long long` 不使用、クラス内 static const 初期化不可。
- 内部は `namespace UkaRegexpImpl`。外に出す型は `uka_regexp.h` のものだけ。ヘッダは STL を include しない。
- 状態の変更は必ず `SetSt()` 経由（undo を積む）。マッチ中に再帰呼び出しをしない。
- 16bit `wchar_t` ではサロゲートペアを 1 文字として扱う。subject の「1 文字」は `DecodeAt()`、1 文字戻るのは `PrevLen()`、ペアの途中かは `IsMidPair()` で判断し、位置を `+1` / `-1` で進めない（32bit では定数に畳まれる）。位置の単位は `wchar_t` のまま。

## 構造（uka_regexp.cpp の順）
Vec/データ構造/文字集合 → `Compiler`（パーサ→構文木 `Node`→`Gen` で int コード）→ `Matcher`（`Run`: 明示スタックのバックトラック VM）→ Unicode 関数 → 生成テーブル → 公開 API。
- `Matcher::st[]` に捕獲・ループカウンタ・\K・現在フレームを全部入れ、`BtEntry` スタックに undo を積む。再帰呼び出し（`OP_CALL`）は `st[]` のスナップショットを取り、`OP_CLOSE` で復元して戻る。
- 定義の無い名前のサブルーチン呼び出しは `Compiler::ResolveExternal()` がコールバックでパターン文字列に解決し、グループとして `MATCH` の後ろに生成する（呼び出し専用）。
- 制御動詞は `BT_VERB` エントリ。戻ってきたら `Run` が false を返し、`Search` が `m_verb` を見て開始位置を進める。
- `Compiler::AnalyzeMemo()` が、状態が (pc, pos) だけで決まるプログラム（後方参照・先読み・atomic・CALL・動詞・\K・回数付きループ無し）の SPLIT / REP / LOOP_TEST に slot を振る。`Run` はバックトラックが `UKA_REGEXP_MEMO_START` 回を超えるとビット表を作り、`BT_MEMO` エントリが pop された（配下が全部失敗した）時にだけ「失敗済み」を記録する。探索中の状態は刈らない（ループの空反復 1 回を許す仕様で捕獲の値が変わるため）。対象を広げたら `make compare-memo` で必ず確かめる。
- `Search` の近道は `Compiler` が作る: `FirstLiteral()`（先頭の固定文字）、`FirstSet()`（最初の 1 文字になりうる集合。制御動詞より前は飛ばさないので、動詞に当たったら使わない）、`RequiredChar()`（どの一致にも必ず含まれる文字）。どれも結果を変えない範囲に限る。`BT_GREEDY` は直後が `OP_CHAR` ならその文字の位置まで飛ぶが、飛ばした位置もステップに数える（上限に当たるかどうかを変えない）。
- 末尾の `// ==== BEGIN GENERATED TABLES` 〜 `END` は `tools/gen_unicode_tables.py` が書き換える（`make unicode-tables`）。手で編集しない。新しい表を参照するときは、先頭の `extern` 宣言を足す。

## テスト（変更したら必ず）
`make test` → `make compare-memo`（失敗の記憶の有無で結果が変わらないこと）→ `make compare-perl`（Perl 5.30+、既知の差分 40 件は `tests/perl_known_diffs.txt`。仕様変更で差分が増減したらそのファイルを意図的に更新）。
大きな変更後は `tests/fuzz_gen.py` のランダムケースを `tests/fuzz_compare.py` で Perl と比べ（Perl は否定先読み内の捕獲を外に漏らす・一部の最適化に不具合があるので、差分は原因を読んで判断する）、`-fsanitize=address,undefined` でも走らせること。
`-std=c++98 -Wall -Wextra -pedantic` で g++ と clang の警告ゼロを保つ。16bit wchar_t は `-fshort-wchar` で確認できる。

## 仕様上の決め事（変えると互換が崩れる。PCRE2 と違う点は元の要件で決まっていたもの）
行区切りは既定で LF のみ／`\d\w\s\b` は既定で ASCII（`UCP` フラグか `(*UCP)` で Unicode）／IGNORECASE は Unicode 単純 case folding／同名グループは同番号／後読みは短い候補から／上限超過は `ERR_STEP_LIMIT`。
