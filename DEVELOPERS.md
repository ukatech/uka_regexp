# 開発者向けドキュメント

`uka_regexp` を C++ のプログラムに組み込む人、エンジン自体を改造する人のための文書です。
正規表現の書き方・対応している構文は [README.md](README.md) にあります。

## 組み込み

`wchar_t` 専用の、C++ 製バックトラック型正規表現エンジンです。外部ライブラリも STL も使いません。
**`uka_regexp.h` と `uka_regexp.cpp` の 2 ファイルをプロジェクトに入れるだけ**で使えます。

- C++98 の範囲で書いてあり、Visual C++ 6.0 や古い GCC から、最近の g++ / clang / MSVC までビルドできます（例外を有効にしてください。VC6 では `/GX`）。
- 複雑なテンプレートは使っていません（内部の小さな配列テンプレートだけ）。
- 再帰を使わずに照合するので、長い入力でも C スタックは溢れません。

## 方針: PCRE2 に近づける

構文と意味は **PCRE2（Perl 互換）に合わせる**ことを基本方針にしています。迷ったときは PCRE2 の挙動を基準にし、PCRE2 のパターンをそのまま、またはわずかな修正で使えることを目指します。
Perl 5.38 との照合テストを用意してあり、PCRE2 / Perl と一致することを確認しています。
意図的に違う点は README の「PCRE2 との関係と意図的な違い」の表に載せています。仕様を変えたら、その表も更新してください。

## 使い方

```cpp
#include "uka_regexp.h"

try {
    CRegexpW re(L"(\\d+)-(\\d+)");            // 不正なパターンなら CRegexpException
    CRegexpContext ctx;                       // マッチ結果と作業領域。スレッドごとに用意する

    if (re.Match(L"tel 03-1234", ctx)) {
        int s = ctx.GetStart(1);              // グループ1の開始位置 (0 は全体)
        int e = ctx.GetEnd(1);                // 終了位置（この位置は含まない）
        bool m = ctx.IsMatched(2);            // グループが参加したか
    }

    CRegexpString out;                        // Replace の出力用の簡易文字列
    int n = re.Replace(L"03-1234", L"$2-$1", out);   // out.c_str() == L"1234-03", n == 1
}
catch (CRegexpException& ex) {
    // ex.GetCode()      ERR_SYNTAX / ERR_STEP_LIMIT / ERR_NOT_COMPILED / ERR_MEMORY
    // ex.GetPosition()  ERR_SYNTAX のときパターン中の位置
    // ex.what()         英語のメッセージ
}
```

### フラグ

コンパイル時に第 2 引数で指定します（`CRegexpW re(L"abc", CRegexpW::IGNORECASE | CRegexpW::MULTILINE)`）。
「パターン内」の列は、同じ指定をパターンの中に書く方法です（README の「オプション」「改行の扱い」を参照）。

| フラグ | パターン内 | 意味 |
|---|---|---|
| `IGNORECASE` | `(?i)` | 大文字と小文字を区別しない |
| `MULTILINE`  | `(?m)` | `^` `$` を行頭・行末に一致させる |
| `SINGLELINE` | `(?s)` | `.` を改行にも一致させる |
| `EXTENDED`   | `(?x)` | パターン中の空白を無視し、`#` から行末までをコメントにする（`[...]` の中は除く） |
| `GLOBAL`     | `(?g)` | `Match()` が前回の続きから探す／`Replace()` が全部置換する |
| `NEWLINE_CR` `NEWLINE_CRLF` `NEWLINE_ANYCRLF` `NEWLINE_ANY` | `(*CR)` など（パターンの先頭） | 改行とみなすもの。既定は LF のみ |
| `BSR_ANYCRLF` | `(*BSR_ANYCRLF)` | `\R` を CR・LF・CRLF だけにする |
| `UCP` | `(*UCP)`（パターンの先頭） | `\d` `\w` `\s` `\b` と POSIX クラスを Unicode のプロパティで判定する（PCRE2 の `PCRE2_UCP`）。既定は OFF（ASCII だけ） |
| `DOLLAR_ENDONLY` | （なし） | `MULTILINE` なしの `$` を、文字列の末尾だけに一致させる（`MULTILINE` と一緒のときは無視。PCRE2 の `PCRE2_DOLLAR_ENDONLY`） |

フラグとパターン内の指定を両方使ったときは、パターン内の指定が、書いた位置から先で上書きします。
`(?g)` はどこに書いても、パターン全体を GLOBAL にします。

### 主な関数

| 関数 | 説明 |
|---|---|
| `CRegexpW(pattern, flags)` / `Compile(pattern, flags)` | コンパイル。失敗しても（`Compile` なら）以前のパターンは保たれる |
| `Match(str, ctx)` | NUL 終端の文字列から最初のマッチを探す |
| `Match(str, len, ctx, start = -1)` | 長さ指定（NUL を含められる）。`start >= 0` ならその位置から探す |
| `MatchExact(str, ctx)` / `MatchExact(str, len, ctx)` | 位置 0 から始まり、文字列の末尾で終わる一致だけを探す（末尾まで届く候補を求めてバックトラックする。`GLOBAL` は無視） |
| `Replace(str, repl, out)` / `Replace(str, len, repl, out)` | 置換。`GLOBAL` なら全部、そうでなければ最初の 1 つ。置換数を返す。`str` や `repl` が `out` 自身の中を指していてもよい |
| `Replace(str, len, repl, out, maxCount, &lastStart, &lastEnd)` | 最大 `maxCount` 個（負なら全部）を、`GLOBAL` に関係なく置換する。`lastStart` / `lastEnd`（省略可）には、最後の置換文字列が `out` の中で占める範囲が入る（置換が無ければ -1） |
| `GetGroupCount()` / `GetGroupNumber(name)` | グループ数（0 番を除く）／名前からの番号（無ければ -1） |
| `SetStepLimit(base, perChar)` | バックトラック上限を変える（下記） |
| `ctx.GetStart(g)` `GetEnd(g)` `IsMatched(g)` `GetGroupCount()` | 結果の取得。文字列そのものは位置から切り出す |
| `ctx.Reset()` | `GLOBAL` の走査位置を 0 に戻す |

置換文字列の書き方（`$1` など）は README の「置換文字列」を参照してください。

- `Match` は文字列中のどこかで最初に一致する部分を探します（先頭固定ではありません）。全体一致にしたいときは `\A...\z` を使うか、`MatchExact` を使ってください。
- `GLOBAL` のとき `start` を省略した `Match()` は、同じ `ctx` での前回の一致の終わりから探し、`while (re.Match(s, ctx)) {...}` で全部の一致を順に取れます。空の一致が続いて止まらないことはありません。失敗すると位置は 0 に戻ります。
- **スレッド**: コンパイル済みの `CRegexpW` は複数スレッドから同時に使えます。`CRegexpContext` はスレッドごとに用意してください。
- **ステップ上限**: `(.*a){12}c` のようなパターンは入力によって指数時間かかるため、バックトラック回数に上限があります。既定は `1000000 + 256 × 入力の長さ` で、超えると `ERR_STEP_LIMIT` の例外が飛びます。`\w+@` を単語文字が何万文字も続く入力に当てるような二乗オーダーのパターンも打ち切られます。バックトラック用スタックにも入力長に比例した上限（`4M + 32 × 長さ` 個）があり、同じ例外になります。パターンの先頭に `(*LIMIT_MATCH=n)` を書くと、回数をそれ以下に下げられます。
- **失敗した状態の記憶**: 後方参照・先読み/後読み・アトミックグループ・サブルーチン呼び出し・制御動詞・`\K`・条件式・回数指定のあるグループのループを含まないパターンでは、1 回の照合でバックトラックが `UKA_REGEXP_MEMO_START`（既定 4096）回を超えると、完全に失敗した（パターンの位置, 入力の位置）を覚え、二度目からは調べません。`(a+)+b` のような指数時間のパターンが多項式時間になります（仕様は README の「制限」）。表の大きさは `命令数 × (入力長 + 1)` ビットで、2^27 ビット（16MB）を超えるときは使いません。

### サブルーチンの外部定義（コールバックによる解決）

`(?&date)` `(?P>date)` `(?R<date>)` `\g<date>` `\g'date'` のようなサブルーチン呼び出しで、パターンの中に定義が無い**名前**は、利用側が渡したコールバックでパターン文字列に解決できます。コールバックが無い、または `false` を返したときは、これまでどおり `ERR_SYNTAX` の例外です。

```cpp
static bool Resolve(const wchar_t* name, CRegexpString& pattern, void* user)
{
    const wchar_t* text = 0;
    if (wcscmp(name, L"d4") == 0)        text = L"\\d{4}";
    else if (wcscmp(name, L"d2") == 0)   text = L"\\d\\d";
    else if (wcscmp(name, L"date") == 0) text = L"(?&d4)-(?&d2)-(?&d2)";   // さらに別の名前を呼んでもよい
    if (!text) return false;                                               // 知らない名前はエラーになる
    pattern.append(text, (int)wcslen(text));                               // エンジンがコピーを持つ
    return true;
}

CRegexpW re(L"^(?&date)$", 0, Resolve, /* user = */ 0);   // 呼ばれるのはコンパイル中、名前ごとに 1 回
```

- 返す文字列は、**その名前のグループの中身**として取り込まれます（`(?(DEFINE)(?<名前>…))` をパターンの最後に足したのと同じ）。自分自身を呼ぶ再帰もできます。
- 取り込まれたグループは、パターン自身のグループの**後ろ**に番号が振られます（`GetGroupCount()` に数えられ、`GetGroupNumber(名前)` で引けます）。サブルーチンの中のグループは、呼び出しから戻ると元に戻るので、結果には現れません。
- 文字列の中のフラグは、`Compile` に渡したフラグから始まります（呼び出し側のパターンの `(?i)` などは引き継ぎません）。文字列の中が不正なら `ERR_SYNTAX`（位置は -1、メッセージにサブルーチン名が入ります）です。
- `pattern` に入れた文字列はエンジンがコピーを持つので、コールバックが返った後は参照されません（呼び出し側で保持し続ける必要はありません）。
- 知らない名前で `false` を返したときの `ERR_SYNTAX` のメッセージには、その名前が入ります（位置は呼び出しの場所）。
- コールバックが例外を投げると、`Compile()` はオブジェクトを変えずにその例外をそのまま伝えます。
- 解決の対象は名前による**呼び出し**だけです。`(?1)` のような番号、`\k<name>` `\g{name}` の後方参照、`(?(name)…)` の条件は、定義が無ければエラーのままです。

### wchar_t のサイズ

`wchar_t` が 32 bit の環境では 1 個が 1 文字、16 bit の環境（Windows）では UTF-16 のサロゲートペアを 1 文字として扱います（詳しくは README の「制限」）。位置（`GetStart()` など）はどちらも `wchar_t` 単位で、16 bit の環境では U+10000 以上の文字が 2 進みます。
テスト（`tests/run_cases.cpp`）は結果の位置をコードポイント単位に直して表示するので、ケースファイルの期待値は 16 bit と 32 bit で共通です。16 bit の確認は Windows で行ってください。

## ビルドとテスト

```sh
make test            # 手書きケース (tests/cases_manual.txt) と API テスト (tests/test_api.cpp)
make compare-perl    # Perl 5.30 以降があれば、tests/cases_perl.txt を Perl の結果と比較
make compare-memo    # 失敗した状態の記憶を最初から使う版と使わない版で、ランダムなパターンの結果を比較（python3 が必要）
```

- `tests/run_cases.cpp` … タブ区切りのケースファイルを実行するランナー（`--verify` で期待値と比較）。
- `tests/cases_perl.txt` … Perl と比べるケース。仕様として違う 40 件は `tests/perl_known_diffs.txt` に記録してあり、増減すると `compare-perl` が知らせます。
- `tests/memo_compare.sh` / `tests/fuzz_memo_gen.py` … `make compare-memo` の本体と、記憶の対象になるパターン（入れ子のループ・空になりうる本体・ループ内の捕獲）の生成器。`-DUKA_REGEXP_MEMO_START=0` で記憶を最初のステップから使うビルドになります。ステップ上限に達していた側だけは差が出てよく、それ以外の差は不具合です。
- `tests/fuzz_gen.py` … Perl と比べるランダムパターンの生成器（`python3 tests/fuzz_gen.py SEED COUNT > file`）。`python3 tests/fuzz_compare.py build/run_cases file` で Perl と比べます（Perl が終わらないケースは飛ばし、グループ 0 の範囲だけを比べます）。
- Unicode のデータ（一般カテゴリ・大文字小文字変換・スクリプト・書記素の分類・二値プロパティ）は `uka_regexp.cpp` の末尾に埋め込んであり、`make unicode-tables`（`tools/gen_unicode_tables.py`）で作り直せます。カテゴリと大文字小文字は Python の `unicodedata` から、それ以外は unicode.org の UCD ファイルから取得します（`tools/ucd/` にキャッシュ、`python3 tools/gen_unicode_tables.py DIR` で取得済みのディレクトリも指定できます）。

### CI（GitHub Actions）

`.github/workflows/ci.yml` が push・プルリクエスト・手動実行で次を行います。

- **build-test**: Linux（g++・clang++）と macOS（clang++）で、本体を `-std=c++98 -Wall -Wextra -pedantic -Werror` でビルドし、`make test` を実行
- **sanitize**: 同じ 3 環境で `-fsanitize=address,undefined` を付けて `make test` と `fuzz_gen.py` のランダムパターン（補助平面の文字を混ぜた `astral` も）を実行（結果は比べず、クラッシュと未定義動作だけを見る）。手元でも `make test BUILD=build/san CXXFLAGS="-std=c++98 -g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"` で同じことができる
- **compare-perl**: Ubuntu の Perl で `make compare-perl`。既知の差分は Perl や Unicode の版で変わりうるため、失敗しても全体は赤にしない

Linux・macOS の `wchar_t` は 32 bit です。16 bit の確認は Windows で行ってください。

ライセンスは `LICENSE` を参照してください。
