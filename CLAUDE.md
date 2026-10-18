# CLAUDE.md

wchar_t 専用のバックトラック型正規表現エンジン。本体は `uka_regexp.h` + `uka_regexp.cpp` の 2 ファイルだけ（使い方・対応構文は README.md）。

## 守ること
- VC6 / 古い GCC でも通る C++98 に限る: STL・C++11・複雑なテンプレート不可、`for (int i…)` で変数を宣言しない（VC6 はスコープが漏れる）、`snprintf` や `long long` 不使用、クラス内 static const 初期化不可。
- 内部は `namespace UkaRegexpImpl`。外に出す型は `uka_regexp.h` のものだけ。ヘッダは STL を include しない。
- 状態の変更は必ず `SetSt()` 経由（undo を積む）。マッチ中に再帰呼び出しをしない。

## 構造（uka_regexp.cpp の順）
Vec/データ構造/文字集合 → `Compiler`（パーサ→構文木 `Node`→`Gen` で int コード）→ `Matcher`（`Run`: 明示スタックのバックトラック VM）→ Unicode 関数 → 生成テーブル → 公開 API。
- `Matcher::st[]` に捕獲・ループカウンタ・\K・現在フレームを全部入れ、`BtEntry` スタックに undo を積む。再帰呼び出し（`OP_CALL`）は `st[]` のスナップショットを取り、`OP_CLOSE` で復元して戻る。
- 末尾の `// ==== BEGIN GENERATED TABLES` 〜 `END` は `tools/gen_unicode_tables.py` が書き換える。手で編集しない。

## テスト（変更したら必ず）
`make test` → `make compare-perl`（Perl 5.30+、既知の差分 44 件は `tests/perl_known_diffs.txt`。仕様変更で差分が増減したらそのファイルを意図的に更新）。
大きな変更後は `tests/fuzz_gen.py` のランダムケースを Perl と比べ、`-fsanitize=address,undefined` でも走らせること。
`-std=c++98 -Wall -Wextra -pedantic` で警告ゼロを保つ。16bit wchar_t は `-fshort-wchar` で確認できる。

## 仕様上の決め事（変えると互換が崩れる）
`$` は末尾のみ（`\Z` が末尾改行の手前）／行区切りは LF のみ／`\d\w\s\b` は ASCII／IGNORECASE は Unicode 単純 case folding／同名グループは同番号／繰り返し内の捕獲は最後の値を保持／後読みは短い候補から／`\g<name>` は参照（呼び出しではない）／上限超過は `ERR_STEP_LIMIT`。
