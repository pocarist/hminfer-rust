# Hindley-Milner type inference by Rust #

このプログラムはScalaで書かれたHindley-Milner型推論のサンプルコードをGroovyで解説されたものを、Rustで書き写したものです。

自分のためにRustの勉強目的で作ったものなので実用性はありません。

こんなテストコードが通る。
```rust
#[test]
fn test_show_type() {
    // 最終的な型判定のテスト群。
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&var("true"))), "Boolean[]");
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&var("xtrue"))), "\n cannot type: xtrue\n reason: undefined: xtrue");
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&var("zero"))), "Int[]");
    let int_list = app(app(var("cons"),
                            var("zero")),
                        var("nil"));
    let zero = var("zero");
    let one = app(var("succ"), var("zero"));
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&int_list)), "List[Int[]]");
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&app(var("isEmpty"), int_list.clone()))), "Boolean[]");
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&app(var("head"), int_list.clone()))), "Int[]");
    assert!(TYPEINFER.with(|ti| ti.show_type(&app(var("tail"), app(var("head"), int_list.clone())))).starts_with("\n cannot type: zero\n reason: cannot unify Int[] with List["));
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&app(var("tail"), app(var("tail"), int_list.clone())))), "List[Int[]]");    // runtime erro but type check is OK
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&app(app(app(var("if"), var("true")), zero.clone()), one.clone()))), "Int[]");
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&app(app(app(var("if"), var("true")), int_list.clone()), one.clone()))), "\n cannot type: succ\n reason: cannot unify List[Int[]] with Int[]");
    let list_len_test = letrec("len",
                                lam("xs",
                                    app(app(app(var("if"),
                                                app(var("isEmpty"), var("xs"))),
                                            var("zero")),
                                        app(var("succ"),
                                            app(var("len"),
                                                app(var("tail"),
                                                    var("xs"))))
                                    )),
                                app(var("len"),
                                    app(
                                        app(var("cons"),
                                            var("zero")),
                                        var("nil"))
                                )
                            );
    assert_eq!(list_len_test.to_string(), "letrec len = λ xs . (((if (isEmpty xs)) zero) (succ (len (tail xs)))) in (len ((cons zero) nil))");
    assert_eq!(TYPEINFER.with(|ti| ti.show_type(&list_len_test)), "Int[]");
}
```

## TODO
- ライブラリ形式にして再利用できる形にする。
- パーサーを用意してmin-mlっぽい言語を作る。

## 感想
- 端的に言ってRust最高。
- このプログラムはマルチスレッドじゃないけど、ボローチェックのおかげでマルチスレッドのときバグ入る気がしない。
- 参照と借用を意識しないとコンパイルが通らないのは最初はつらかったけど、だんだん分かってきた。体がボローチェック養成ギブスで固められた感じ。
- 関数の引数をrefにするかmoveにするか迷う。どういう基準で選べばいいんだろう。

## 感謝
Groovyの解説を書いてくれた@uehajさん、ありがとうございました。

