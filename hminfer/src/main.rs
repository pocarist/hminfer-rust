//Groovy: 
/**
 * Hindley-Milner type inference
 * Ported to Groovy from Scala by Example Chapter 16 code.
 * (http://www.scala-lang.org/docu/files/ScalaByExample.pdf)
 * refered also
 * https://github.com/namin/spots/blob/master/hindleyMilner/typeInference.scala
 * Japanese page of 'Scala by Example':
 * http://www29.atwiki.jp/tmiya/pages/78.html
 */
//Rust:
/**
 * Hindley-Milner type inference
 * Ported to Rust from Groovy.
 * http://uehaj.hatenablog.com/entry/2014/02/01/183039
 */

use std::fmt; // Import `fmt`
use std::collections::BTreeMap;
use std::iter::{Iterator};
use std::cell::{Cell,RefCell};
use std::error::Error;

mod util {
    use std::fmt;
    use std::collections::BTreeSet;

    //Rust: Vecの引き算を定義。
    //TODO: 本当はstd::ops::SubのTraitを実装した形にしたかったが、Vec<T>でのやり方がわからなかった。
    pub fn sub_vec<T>(lhs: Vec<T>, rhs: &Vec<T>) -> Vec<T> where T: Ord + Clone {
        let mut s = BTreeSet::new(); 
        for i in rhs {
            s.insert(i);
        }
        let mut lhs = lhs;
        lhs.retain(|i| !s.contains(i));
        lhs
    }

    //Rust: Vecを文字列化。
    //TODO: 自分で定義しなくても、すでにあるような気がするがよくわからなかった。
    pub fn vec_to_string<T>(xs : &Vec<T>) -> String where T: fmt::Display {
        format!("[{}]", xs.iter().map(|x| format!("{}",x)).collect::<Vec<_>>().join(","))
    }
}

#[derive(Debug,PartialEq)]
struct TypeError(String);

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Error for TypeError {
    fn description(&self) -> &str {
        &self.0
    }
}

//Rust: GroobyはTermをベースクラスにして各Termを派生させているが、RustではTermというenumにした。
/**
 * Termおよびそのサブクラスによって構文木を構成する項を定義する。
 * 項とは以下のいずれか。
 *   - 変数(Var)
 *   - λ抽象(Lambda)
 *   - 関数適用(App)
 *   - let式(Let)
 *   - letrec式(LetRec)
 */
#[derive(Debug,PartialEq,Clone)]
pub enum Term {
    Var(String),
    Lam(String,Box<Term>),
    App(Box<Term>,Box<Term>),
    Let(String,Box<Term>,Box<Term>),
    LetRec(String,Box<Term>,Box<Term>)
}

// Implement `Display` for `Term`.
impl fmt::Display for Term {
    fn fmt(&self, fp: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Term::Var(ref x) => write!(fp, "{}", x),
            &Term::Lam(ref x, ref e) => write!(fp, "λ {} . {}", x, e),
            &Term::App(ref f, ref e) => write!(fp, "({} {})", f, e),
            &Term::Let(ref x, ref e, ref f) => write!(fp, "let {} = {} in {}", x, e, f),
            &Term::LetRec(ref x, ref e, ref f) => write!(fp, "letrec {} = {} in {}", x, e, f),
        }
    }
}

//Rust: to_string()とBox::new()を書かなくてすますためのお助け関数
mod util_term {
    use Term;
    pub fn var(x: &str) -> Term { Term::Var(x.to_string()) }
    pub fn lam(x: &str, e: Term) -> Term { Term::Lam(x.to_string(), Box::new(e)) }
    pub fn app(f: Term, e: Term) -> Term { Term::App(Box::new(f), Box::new(e)) }
    pub fn let_(x: &str, e: Term, f: Term) -> Term { Term::Let(x.to_string(), Box::new(e), Box::new(f)) }
    pub fn letrec(x: &str, e: Term, f: Term) -> Term { Term::LetRec(x.to_string(), Box::new(e), Box::new(f)) }
}
use util_term::*;

//Rust: Termに同じ。しかし、TyvarだけはTypeの派生として扱いたかったが、type Tyvar=Stringでお茶を濁す
/**
 * Typeおよびそのサブクラスによって式木の構成要素を定義する。
 * 型とは以下のいずれか。
 *  - 型変数(Tyvar)
 *  - 関数型(Arrow)
 *  - 型コンストラクタ呼び出し(Tycon)(具体型)
 * 型変数を含む型を多相型と呼ぶ。
 */
#[derive(Debug,PartialEq,Clone,Eq,PartialOrd,Ord)]
pub enum Type {
    Tyvar(Tyvar),
    Arrow(Box<Type>, Box<Type>),
    Tycon(String, Vec<Type>),
}
type Tyvar = String;    

// Implement `Display` for `Type`.
impl fmt::Display for Type {
    fn fmt(&self, fp: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Type::Tyvar(ref x) => write!(fp, "{}", x),
            &Type::Arrow(ref t1, ref t2) => write!(fp, "({} -> {})", t1, t2),
            &Type::Tycon(ref k, ref ts) => write!(fp, "{}[{}]", k, ts.iter().map(|x| format!("{}",x)).collect::<Vec<_>>().join(",")), 
        }
    }
}

mod util_type {
    use Type;
    pub fn tyvar(a: &str) -> Type { Type::Tyvar(a.to_string()) }
    pub fn arrow(a: Type, b: Type) -> Type { Type::Arrow(Box::new(a), Box::new(b)) }
    pub fn tycon(a: &str, b: Vec<Type>) -> Type { Type::Tycon(a.to_string(), b) }
}
use util_type::*;

//Rust: Groobyではクラスの継承でEmptyとExtendを表していたがこれもenumで書き換え。
//TODO: 本当はstd::ops::FnのTraitを実装した形にしたかった。でもenumの値にFn()を適用ってできないのかな？
/**
 * Substは「型に含まれる型変数の置換処理」を表わす。
 * Subst represent a step of substitution of type variables of polymorphic type.
 *
 * Substはcallメソッドが定義されているので、Subst(のサブクラス)のイ
 * ンスタンスに対して関数のように呼び出すことができる(Groovyの機能)。
 * 例えばx = new Subst(); x(..)と呼べるということ。
 * 2種類の引数の型に対してcallが定義されている。
 * 
 *  - call(Type)
 *    型中に含まれる型変数を置換する。
 *  - call(Env)
 *    Envに含まれるすべての型スキーマに含まれる型変数を置換したEnvを返す。
 * 
 * 実装機構としては、Substのサブクラスのインスタンス1つは、「Innerクラ
 * ス→内部クラスを含むOuterクラスのインスタンス」、それをまた含む
 * Outerクラス…というチェインを構成する。そのチェインは複数の置換処理
 * を連鎖である。callはOuterクラスのcallを呼び、という再帰処理が行なわ
 * れるので、複数の置換が適用できる。Innerクラスのインスタンスを作成す
 * るには、extendを呼ぶ。
 */
#[derive(Debug,PartialEq,Clone)]
enum Subst {
    Empty,
    Extend(Box<Subst>, Tyvar, Type),
}

impl Subst {
    /**
     * 指定した型変数の置換結果を返す。
     * SubstのOuter/Innerクラス関係から構成されるチェインを辿って探す。
     */
    fn lookup(&self, t : &Type) -> Type {
        match t {
            &Type::Tyvar(ref a) => self.lookup_tyvar(a),
            _ => panic!("InvalidCastException!"),
        }
    }
    fn lookup_tyvar(&self, y : &Tyvar) -> Type {
        match self {
            &Subst::Empty => Type::Tyvar(y.clone()),
            &Subst::Extend(ref parent, ref x, ref t) => {
                if x == y { t.clone() }
                else { parent.lookup_tyvar(y) }
            }
        }
    }

    /**
     * 型Type t中に含まれる型変数を置換した結果の型を返す。
     * 型に含まれる型変数(つまり多相型の型変数)の変数を、変化しなく
     * なるまでひたすら置換する。置換の結果がさらに置換可能であれば、
     * 置換がなされなくなるまで置換を繰り返す。(循環参照の対処はさ
     * れてないので現実装は置換がループしてないことが前提)。
     */
    fn call(&self, t : &Type) -> Type {
        match t {
            &Type::Tyvar(ref a) => {
                let u = self.lookup_tyvar(a);
                if t == &u { u } else { self.call(&u) }                
            },
            &Type::Arrow(ref t1, ref t2) =>
                arrow(self.call(t1), self.call(t2)),
            &Type::Tycon(ref k, ref ts) =>
                Type::Tycon(k.clone(), ts.iter().map(|i|self.call(i)).collect()),
        }
    }

    /**
     * 環境Env eに含まれるすべての型スキーマに含まれる型変数を置換した
     * Envを返す。
     */
    fn call_env(&self, env : &Env) -> Env {
        env.clone().into_iter().map(|(x,ts)| (x, TypeScheme::new(ts.tyvars, self.call(&ts.tpe)))).collect()
    }

    /**
     * Innerクラスのインスタンスを生成する操作がextend()であり、「1つの
     * 型変数を一つの型へ置換」に対応するインスタンス1つを返す。ただし
     * extendで生成されたインスタンスは、extendを呼び出した元のオブジェ
     * クト(extendにとってのthisオブジェクト) =Outerクラスのインスタン
     * スとチェインしており、さらにcallにおいて、Outerクラスを呼び出し
     * て実行した置換の結果に対して追加的に置換を行うので、元の置換に対
     * して「拡張された置換」になる。
     */
    fn extend(self, x: Type, t: Type) -> Subst {
        match x {
            Type::Tyvar(a) => self.extend_tyvar(a, t),
            _ => panic!("InvalidCastException!"),
        }
    }
    fn extend_tyvar(self, x: Tyvar, t: Type) -> Subst {
        Subst::Extend(Box::new(self), x, t)
    }

    /**
     * 初期値としての空の置換を返す。
     * 任意のSubstインスタンスについて、OuterクラスのOuterクラスの…
     * という連鎖の最終端となる。
     */
    fn empty() -> Subst {
        Subst::Empty
    }
}

impl fmt::Display for Subst {
    fn fmt(&self, fp: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Subst::Empty => write!(fp, "(empty)"),
            &Subst::Extend(ref parent, ref x, ref t) => {
                write!(fp, "{}\n{}={}", parent.to_string(), x, t)
            }
        }
    }
}

/**
 * TypeSchemeは、型抽象(∀X.T)を表わす。
 * 型抽象とは、「型引数」を引数に取り、型変数を含むテンプレートのよう
 * なものを本体とするような、λ式のようなもの。
 *
 * TypeSchemeはTypeを継承していない。その結果、Typeの構造の途中に
 * TypeSchemeが表われることもない。
 *
 * Haskellの「forall.」は型スキーマ(型抽象)に対応しているが、このHMアル
 * ゴリズムでは型スキーマ(抽象)はトップレベルの環境における識別子に直接
 * 結びつく形でしか存在しない。つまりランクN多相を許していない。
 *
 * もしTypeSchemeが型の一種であり、型構造の任意の部分に表われ得るなら
 * (つまりmgu()やtp()の型推定の解決対象の型コンストラクタなら)、ランク
 * N多相が実現されることになる。
 */
#[derive(Debug,PartialEq,Clone)]
struct TypeScheme {
    /**
     * tyvarsは型抽象において全称量化された型変数の集合を表す。
     * tyvars are set of universally quantified types in the type scheme.
     *
     * tyvarsは「その外側に対して名前が衝突しないことの保証」を持った型
     * 変数である。なぜなら型スキーマの使用に際してnewInstance()するこ
     * とでtpe中でのtyvars変数の使用がリネームされるからである。
     *
     * 具体的には、プログラム中にVar(x)の形で識別子xが使用されるとき、
     * 識別子xの型を得るために、環境に登録された「xに対応する型スキーマ」
     * を取得した上で、Type型に変換する処理(TypeScheme.newInstance())が
     * 行なわれる。newInstance()は、tpe中のtyvarsと同じ名前を持った変数
     * を、すべて重ならない新規の名前にリネーム置換したバージョンのtpe
     * を返す。
     */
    tyvars : Vec<Type>,

    /**
     * 型のテンプレートを表わす。全称量化されている型変数と同じ型変数を
     * 含んでいれば、その型変数は、型スキーマがインスタンス化されるとき
     * に重ならない別名に置換される。
     */
    tpe : Type,
}

impl TypeScheme {
    /**
     * 型スキーマ(型抽象)を型に具体化する操作。
     *
     *    newInstance: TypeSchema → Type
     *
     * ちなみにgen()は反対に型から型スキーマを生み出す操作である。
     *
     *    gen: Type → TypeSchema
     * 
     * newInstance()は、全称限量指定された変数およびそれに束縛された変
     * 数(つまりフリー型変数を除いた全ての型変数)の使用を、新規の変数名
     * にリネームする。この操作の結果は、環境には左右されず、
     * TypeSchemeインスタンスのみの情報によって確定される。(変数名のシー
     * ドとなるtypeInfer.nの値には依存するが)
     * 
     * newInstance()の結果として得られる型には全称限量で指定されていた
     * 型変数は含まれない。たとえば、型スキーマ
     * 
     *    TypeSchema s = ∀ a,b . (a,b型を含む型)
     * 
     * に対して、newInstanceした結果は、
     * 
     *      s.newInstance() = (a',b'型を含む型)
     * 
     * であり、a,bは、a'b'に置換されるので、結果の型には決して現われな
     * い。
    */
    fn new_instance(&self) -> Type {
        self.tyvars.iter().fold(Subst::empty(), |s, t| {s.extend(t.clone(), TYPEINFER.with(|ti| ti.new_tyvar()) )}).call(&self.tpe)
    }

    fn new(tyvars : Vec<Type>, tpe : Type) -> TypeScheme {
        TypeScheme{tyvars:tyvars, tpe:tpe}
    }
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, fp: &mut fmt::Formatter) -> fmt::Result {
        write!(fp, "∀ ({}) . ({})", self.tyvars.iter().map(|x| format!("{}",x)).collect::<Vec<_>>().join(","), self.tpe)
    }
}

//Rust: 最初、安直にHashMapで実装したらテストに時々失敗した。Rustのハッシュって文字列(String)でハッシュ値変わるのか？
//TODO: 連想リストにしたらどうなるか実験したい。
/**
 * 環境Envは、プログラムのある位置における、識別子と型情報(型スキー
 * マ)の対応表である。
 * Env is map of identifier to type schema.
 * 環境Envは、意味的には型変数を含む制約の集合と見做すことができる。
 * Env can be regarded as set of constraints of relationships concerning
 * types include type variables. So HM type checker is constraints solver for it.
 * 環境は、tp()が解くべき、型方程式の制約条件を表現している。
 *     Env: 「プログラム中の識別子→型スキーマ」の対応の集合
 * 
 * ちなみに、Substもある種の対応表であるが、型変数の書き換えルールの
 * 集合。
 * 
 *     Subst: 「型変数→型(型変数|Arrow|Tycon)」という書き換え規則の集合
 * 
 * なお、明かにこの実装は空間効率が悪い。Scalaではタプルのリスト(連想リ
 * スト)で実現されていたところをGroovy化する際に、安易にMapにしてコピー
 * して受け渡すようにしたが、実用的には連想リストにすべき。
 */
type Env = BTreeMap<String, TypeScheme>;


//Rust: 標準だけでシングルトンを作るのが難しかったのでthred_loaclでお茶を濁す
/**
 * TypeInferはHM型推論の全体を含む。Scalaではオブジェクトだったので、
 * @SIngletonとして定義してある。サービスメソッドを呼び出すための静的
 * import可能な変数として、static typeInferを容易してある。
 * 型チェックの全体の流れは、
 *
 * showType ->  predefinedEnv
 *          ->  typeOf         ->    tp  ->  mgu
 *
 * である。
 */
#[derive(Debug)]
struct TypeInfer {
    /**
     * エラーメッセージに含めるための、処理中の項への参照。
     */
    current: RefCell<Option<Term>>,
    n: Cell<u32>,
}
impl TypeInfer {
    fn new() -> TypeInfer {
        TypeInfer {current:RefCell::new(None),n:Cell::new(0)}
    }

    fn reset(&self) {
        self.n.set(0);
    }

    /**
     * 名前が重ならない新規の型変数を作成する。
     */
    fn new_tyvar(&self) -> Type {
        let n = self.n.get();
        self.n.set(n+1);
        Type::Tyvar(format!("a{}", n))
    }

    //Rust: 引数のxを&Stringにできないのは何でなの？
    /**
     * 環境中にで定義された識別子xに対応する型スキーマを取得する。
     */
    fn lookup(e: &Env, x: String) -> Option<&TypeScheme> {
        e.get(&x)
    }

    /**
     * 型tに含まれているすべての型変数の集合(A)から、この環境に登録され
     * ているすべての型スキーマの「全称量化に関するフリー型変数の集合
     * (※1)」=(B)を除外したもの((A)-(B))を全称量化することで型スキーマ
     * を生成する。
     *
     * (※1)λx.yのとき変数xに束縛されていることを「λ束縛」と呼び、
     *     「λ束縛されていない変数」をフリー変数と呼ぶが、それと同様に、
     *     型変数に関する∀y...のとき型変数yに束縛されていることを「全
     *     称量化束縛」と呼び、「全称量化束縛」されていない型変数を「全
     *     称量化に関するフリー型変数」とする(ここで作った言葉)。
     *
     * 環境において「全称量化に関するフリー型変数」が発生するケースとい
     * うのは、具体的にはラムダ式
     *
     *    λ x . y
     *
     * において、識別子xに対応する型は、新規の型変数として環境に登録さ
     * れ、そのもとでyが型推論されるが、y解析中でのxの登場はスキーマ内
     * で全称量化されていない、という状態である。
     */
    fn gen (&self, env: &Env, t: Type) -> TypeScheme {
        // new TypeScheme(this.tyvars(t) -- this.tyvars(env), t)
        let tvs = self.tyvars(t.clone());
        let v = util::sub_vec(tvs, &self.tyvars_env(env));
        TypeScheme::new(v, t)
    }

    /**
     * 型に対するtyvars()は、指定した型Type t中に含まれる型変数のリスト
     * を返す。
     */
    fn tyvars (&self, t : Type) -> Vec<Type> {
        match t {
            Type::Tyvar(_) => {vec![t]}
            Type::Arrow(t1, t2) => {
                let mut v1 = self.tyvars(*t1);
                let ref mut rv2 = self.tyvars(*t2);
                v1.append(rv2);
                v1
            }
            Type::Tycon(_, ts) => {
                ts.into_iter().fold(vec![], |mut tvs, elem| {
                    tvs.append(&mut self.tyvars(elem));
                    tvs
                })
            }
        }
    }

    /**
     * 型スキーマに対するtyvars()は、指定した型スキーマTypeSchema tsの
     * 型テンプレート(ts.tpe)が使用している型変数から、全称量化された変
     * 数(ts.tyvars)を除外したものを返す。これは、何かというと、型スキー
     * マの型テンプレート(TypeSchema.tpe)が含む「全称量化に関するフリー
     * 型変数)の集合」である。
     */
    fn tyvars_typescheme(&self, ts: TypeScheme) -> Vec<Type> {
        let tvs = self.tyvars(ts.tpe);
        util::sub_vec(tvs, &ts.tyvars)
    }

    /**
     * 環境Envに対するtyvarsは、その環境に登録されているすべての型スキー
     * マに対するtvarsの値全体を返す。
     * つまり、環境全体が含む「全称量化に関するフリー変数の集合」を返す。
     */
    fn tyvars_env(&self, env: &Env) -> Vec<Type> {
        env.iter().fold(vec![], |mut s, (_, v)| {s.append(&mut self.tyvars_typescheme(v.clone())); s})
    }
    
    /**
     * 型tと型uのユニフィケーション。
     * 型tと型uに対してs'(t) s'(u)が一致するような、sを拡張した置換s'
     * を返す。
     */
    fn mgu(&self, t: &Type, u: &Type, s: Subst) -> Result<Subst, TypeError> {
        let (st, su) = (s.call(t), s.call(u));
        match (st, su) {
            (Type::Tyvar(ref stv), Type::Tyvar(ref suv)) if stv == suv => Ok(s), 
            (Type::Tyvar(stv), su1 @ _) => Ok(s.extend_tyvar(stv,su1)), 
            (t1 @ _, u1 @ Type::Tyvar(_)) => self.mgu(&u1,&t1,s), 
            (Type::Arrow(ref st1, ref st2), Type::Arrow(ref su1, ref su2)) => {
                self.mgu(su2, st2, s).and_then(|s1| self.mgu(su1, st1, s1))
            },
            (Type::Tycon(ref kt, ref tst), Type::Tycon(ref ku, ref tsu)) if kt == ku => {
                //Rust: なんか効率悪そうなコード。普通にループまわしたほうが良さそう。
                //moveでキャプチャしたいけど、ガードで変数を参照しているからダメって言われる。律儀な奴だ。
                TypeInfer::zip(tst.clone(), tsu.clone()).and_then(|v|v.iter().fold(Ok(s), |acc, xy| acc.and_then(|s1| self.mgu(&xy.0, &xy.1, s1))))
            },
            (st1 @ _, su1 @ _) => Err(TypeError(format!("cannot unify {} with {}", st1, su1)))
        }
    }

    /**
     * 二つのリストxs=[x1,x2,x3..], ys=[y1,y2,y3]のとき、
     * [[x1,y1],[x2,y2],[x3,y3]..]を返す。
     */
    fn zip<T,U>(xs: Vec<T>, ys: Vec<U>) -> Result<Vec<(T,U)>, TypeError> where T: fmt::Display, U: fmt::Display {
        if xs.len() == ys.len() {
            let zipper: Vec<_> = xs.into_iter().zip(ys.into_iter()).collect();
            Ok(zipper)
        } else {
            Err(TypeError(format!("cannot unify {} with {}, number of type arguments are different", util::vec_to_string(&xs), util::vec_to_string(&ys))))
        }
    }

    /**  
     *  envのもとで、eの型がt型に一致するためのsを拡張した置換s'を返す。
     *  数式で書くと以下のとおり。
     *
     *    s'(env) ├ ∈ e:s'(t)
     *  
     *  つまり、型の間の関係制約式(型変数を含む)の集合envのもとで、「eの型はtで
     *  ある」を満たすような、sを拡張した置換s'を値を返す。
     */
    fn tp (&self, env: &Env, e: &Term, t: &Type, s: Subst) -> Result<Subst, TypeError> {
        *self.current.borrow_mut() = Some(e.clone());
        match e {
            &Term::Var(ref x) => {
                // 変数参照eの型は、eの識別子e.xとして登録された型スキーマを実体化(全称量
                // 化された変数のリネーム)をした型である。
                match TypeInfer::lookup(&env, x.clone()) {
                    None => Err(TypeError(format!("undefined: {}", x))),
                    Some(u) => self.mgu(&u.new_instance(), &t, s),
                }
            }
            &Term::Lam(ref x, ref ee) => {
                // λで束縛される変数とletで束縛される変数の扱いの違いにつ
                // いて。
                // 変数(識別子)は、HMの多相型の解決において、キーとなる存在
                // である。型スキーマは変数(識別子)にのみ結びつく。変数を介
                // 在して得た型スキーマを基軸に、インスタンス化=全称量化=型
                // 変数置換が実行される。
                //
                // 識別子x,yに束縛される式が多相型であるとき、型変数の解決
                // の扱いに関して両者には違いがある。
                //
                // λx.eの場合、xに対応して環境に登録されるのは、xの型を表
                // わす新規の型変数(a = newTyvar())を型テンプレートとする型
                // スキーマ(型抽象)であり、かつaについては全称限量されない。
                // つまり「全称量化に関するフリー型変数を含む型スキーマ」に
                // なっている。
                //
                // let y=e1 in e2の場合、yに対応して環境に登録されるのは、
                // e1の型を元にして、e1中の型変数群
                // 
                // 「e1.tyvars-tyvars(e1.e)」…(*)
                // 
                // を全称限量した型スキーマ(型抽象)。例えば「new
                // TypeScheme(tyvars(e1), e1)」が登録される。(*)における、
                // tyvars(e1.e)は、e1中のフリー型変数だが、これが生じるのは、
                // λ束縛の本体の型検査の場合である。つまり
                //
                //   \ x -> let y=e1 in e2
                //
                // のように、λ本体の中にlet式が出現するときに、let束縛され
                // る識別子yのために登録される型スキーマでは、xに対応する型
                // スキーマで使用されている型変数がフリーなので全称限量対象
                // から除外される。
                // 
                // [ここでのλとletの違いがどのような動作の違いとして現われるか?]
                // 
                // Haskellで確認する。
                // 
                // ghci> let x=length in x [1,2,3]+x "abc"
                // 6
                // ghci> (\ x -> x [1,2,3]+x "abc") length
                //         <interactive>:5:12:
                //     No instance for (Num Char)
                //       arising from the literal `1'
                //     Possible fix: add an instance declaration for (Num Char)
                //     In the expression: 1
                //     In the first argument of `x', namely `[1, 2, 3]'
                //     In the first argument of `(+)', namely `x [1, 2, 3]'
                //
                // letでのxに束縛された多相関数lengthの型(a->a)における型変
                // 数aは全称限量されるので、「x [1,2,3]」と「x "abc"」それ
                // ぞれにおけるxの出現それぞれでaがリネームされ(1回目はa',
                // 二回目はa''など)、別の型変数扱いになる。そのため、a'と
                // a''がそれぞれのIntとCharに実体化されても、型エラーになら
                // ない。
                // 
                // λの場合、xの型は全称限量されない(a->a)なので、a=Intと
                // a=Charの型制約が解決できず型エラーとなる。この動作はテス
                // トケースtestTpLamP2()、testTpLetP1() で確認する。
                let (a, b) = (self.new_tyvar(), self.new_tyvar());
                self.mgu(t, &arrow(a.clone(), b.clone()), s).and_then(|s1| {
                    let mut env1 = env.clone(); 
                    env1.insert(x.clone(), TypeScheme::new(vec![], a));
                    self.tp(&env1, ee, &b, s1)
                })
            }
            &Term::App(ref f, ref ee) => {
                let a = self.new_tyvar();
                self.tp(env, f, &arrow(a.clone(), t.clone()), s).and_then(|s1|{
                    self.tp(env, ee, &a, s1)
                })
            }
            &Term::Let(ref x, ref ee, ref f) => {
                // λ x ...で束縛される変数とlet x= ..in..で束縛され
                // る変数の違いについては前述の通り。                
                let a = self.new_tyvar();
                match self.tp(env, ee, &a, s) {
                    Ok(s1) => {
                        let ts = self.gen(&s1.call_env(env), s1.call(&a));
                        let mut env1 = env.clone(); 
                        env1.insert(x.clone(), ts);
                        self.tp(&env1, f, t, s1)
                    }
                    err => err
                }
            }
            &Term::LetRec(ref x, ref ee, ref f) => {
                let (a, b) = (self.new_tyvar(), self.new_tyvar());
                let mut env1 = env.clone(); 
                env1.insert(x.clone(), TypeScheme::new(vec![], a.clone()));
                match self.tp(&env1, ee, &b, s) {
                    Ok(s1) => {
                        match self.mgu(&a, &b, s1) {
                            Ok(s2) => {
                                let mut env2 = env.clone(); 
                                env2.insert(x.clone(), self.gen(&s2.call_env(env), s2.call(&a)));
                                self.tp(&env2, f, t, s2)
                            }
                            err => err
                        }
                    }
                    err => err
                } 
            }
        }
    }

    /**
     * 環境envにおいてTerm eの型として推定される型を返す。
     */
    fn type_of(&self, env: &Env, e: &Term) -> Result<Type,TypeError> {
        let a = self.new_tyvar();
        self.tp(env, e, &a, Subst::empty()).map(|s1| s1.call(&a))
    }

    //Rust: clone()を何回も書きそうになったので参照に変えてみた。余計分からなくなったという説あり。
    /**
     * 既定義の識別子(処理系の組み込み関数もしくはライブラリ関数を想定)を
     * いくつか定義した型環境を返す。型のみの情報でありそれらに対する構
     * 文木の情報はない。
     */
    fn predefined_env(&self) -> Env {
        let boolean_type = tycon("Boolean", vec![]);
        let int_type = tycon("Int", vec![]);
        let list_type = |t:&Type| tycon("List", vec![t.clone()]);
        let gen = |t:&Type| self.gen(&Env::new(), t.clone());
        let arrow = |t1:&Type,t2:&Type| arrow(t1.clone(), t2.clone());
        let a = self.new_tyvar();
        [("true",gen(&boolean_type)),
        ("false",gen(&boolean_type)),
        ("if",gen(&arrow(&boolean_type, &arrow(&a, &arrow(&a, &a))))),
        ("zero",gen(&int_type)),
        ("succ",gen(&arrow(&int_type, &int_type))),
        ("nil",gen(&list_type(&a))),
        ("cons",gen(&arrow(&a, &arrow(&list_type(&a), &list_type(&a))))),
        ("isEmpty",gen(&arrow(&list_type(&a), &boolean_type))),
        ("head",gen(&arrow(&list_type(&a), &a))),
        ("tail",gen(&arrow(&list_type(&a), &list_type(&a)))),
        ("fix",gen(&arrow(&arrow(&a, &a), &a)))]
        .iter()
        .cloned()
        .map(|(k,v)| (k.to_string(), v))
        .collect()
    }
    
    /**
     * 項の型を返す。
     */
    fn show_type(&self, e: &Term) -> String {
        match self.type_of(&self.predefined_env(), e) {
            Ok(t) => t.to_string(),
            Err(ex) => {
                if let Some(ref e) = *self.current.borrow() { // deref
                    format!("\n cannot type: {}\n reason: {}", e.to_string(), ex.description())
                } else {
                    format!("\n cannot type: None\n reason: {}", ex.description())
                }
            }
        }  
    }
}

//Rust: Rustはグローバル変数は全部大文字にするみたい？
/**
 * @Singleton宣言したクラスのシングルトンはTypeInfer.instanceで保持
 * されており、クラス外からも取得できる。しかし、
 * 「TypeInfer.instance」が少し冗長なのと、Scala版に合せるため、シ
 * ングルトンを以下で定義する静的変数TypeInfer.typeInferで取得でき
 * るようにする。ただしSingletonの初期化タイミングの都合上か、遅延
 * 設定のAST変換@Lazyを指定しないとうまくいかないようである。
 */
thread_local!(
    static TYPEINFER: TypeInfer = TypeInfer::new();
);

fn main() {
    //Rust: 警告が出なくなるまでテストコードを呼ぶ。なにも起こらない。

    // fn test_type_scheme_new_instance1()
    {
        // 型スキーマをnewInstance()するときに型変数が置換されることの確認
        TYPEINFER.with(|ti| ti.reset());
        let ts = TypeScheme::new(vec![tyvar("a"), tyvar("b")], tyvar("a"));
        // where 'a' is bounded
        assert!(ts.tyvars == [tyvar("a"), tyvar("b")]);
        assert!(ts.tpe == tyvar("a"));
        assert!(ts.to_string() == "∀ (a,b) . (a)");
        let t1 = ts.new_instance(); // 'a' of ts1.tpe is replaced to 'a0'
        assert!(t1.to_string() == "a0");
    }
    // fn test_subst_lookup2()
    {
        // substの羃等性をチェック。置換対象ではない型変数はそのものが返る。
        let subst0 = Subst::empty();
        let subst1 = subst0.clone().extend(tyvar("a"), tyvar("b"));
        assert!(subst0.lookup(&tyvar("a")) == tyvar("a"));  // subst0は変化していない
        assert!(subst0 != subst1);
        assert!(subst1.lookup(&tyvar("a")) == tyvar("b")); // a == b
        assert!(subst1.lookup(&tyvar("b")) == tyvar("b")); // b == b
    }
    
    // fn test_tp_lam_let1() 
    {
        //  [e1:Bool, 1:Int] |- (\ x -> let y=e1 in x) 1 : Int
        //
        // 「 \ x -> let y=e1 in x」のように、λ本体の中にlet式が出現す
        // るときに、let束縛される識別子yのために登録される型スキーマで
        // は、xに対応する型スキーマで使用されている型変数が全称限量対
        // 象から除外される。
        // let mut env = Env::new();
        // env.insert("e1".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
        // env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
        let env : Env = [("e1", TypeScheme::new(vec![], tycon("Boolean",vec![]))),
            ("1", TypeScheme::new(vec![], tycon("Int",vec![])))]
            .into_iter()
            .cloned()
            .map(|(k,v)| (k.to_string(), v))
            .collect();
        let typ = tyvar("a");
        let subst = TYPEINFER.with(|ti| ti.tp(&env, 
                                                &app(
                                                    lam("x",
                                                        let_("y", var("e1"), var("x"))),
                                                    var("1")
                                                ), &typ, Subst::empty())).unwrap();
        assert_eq!(subst.call(&typ), tycon("Int", vec![]));
    }
    
    //fn test_show_type()
    {
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
    
}

#[test]
fn test_sub_vec() {
    // Vec<T>の引き算をテスト
    let v1 = vec![tyvar("3"), tyvar("1"), tyvar("4")];
    let v2 = vec![tyvar("1"), tyvar("5"), tyvar("9")];
    let a = util::sub_vec(v1, &v2);
    assert_eq!(a, vec![tyvar("3"), tyvar("4")]);
}

#[test]
fn test_terms() {
    // 構文木の試験。
    assert_eq!(var("a").to_string(), "a");
    assert_eq!(lam("a", var("b")).to_string(), "λ a . b");
    assert_eq!(app(var("a"), var("b")).to_string(), "(a b)");
    assert_eq!(let_("a", var("b"), var("c")).to_string(), "let a = b in c");
    assert_eq!(letrec("a", var("b"), var("c")).to_string(), "letrec a = b in c");
}

#[test]
fn test_terms_equals() {
    // 構文木に対する@Immutableが生成した自明なequalsの動作を確認(一致する場合)。
    assert_eq!(var("a"), var("a"));
    assert_eq!(lam("a", var("b")), lam("a", var("b")));
    assert_eq!(app(var("a"), var("b")), app(var("a"), var("b")));
    assert_eq!(let_("a", var("b"), var("c")), let_("a", var("b"), var("c")));
    assert_eq!(letrec("a", var("b") ,var("c")), letrec("a", var("b"), var("c")));
}

#[test]
fn test_terms_not_equals() {
    // 構文木に対する@Immutableが生成した自明なequalsの動作を確認(一致しない場合)。
    assert_ne!(var("a"), var("a0"));
    assert_ne!(lam("a", var("b")), lam("a", var("b0")));
    assert_ne!(app(var("a"), var("b")), app(var("a"), var("b0")));
    assert_ne!(let_("a", var("b"), var("c")), let_("a", var("b"), var("c0")));
    assert_ne!(letrec("a", var("b") ,var("c")), letrec("a", var("b"), var("c0")));
}

#[test]
fn test_types() {
    // 型の構成要素に対する@Immutableが生成した自明なtoStringの動作を確認。
    assert_eq!(tyvar("a").to_string(), "a");
    assert_eq!(arrow(tyvar("a"), tyvar("b")).to_string(), "(a -> b)");
    assert_eq!(tycon("A", vec![]).to_string(), "A[]");
    assert_eq!(tycon("A", vec![tyvar("b")]).to_string(), "A[b]");
    assert_eq!(tycon("A", vec![tyvar("b"),tyvar("c")]).to_string(), "A[b,c]");
}

#[test]
fn test_types_equals() {
    // 型の構成要素に対する@Immutableが生成した自明なequalsの動作を確認。
    assert_eq!(tyvar("a"), tyvar("a"));
    assert_eq!(arrow(tyvar("a"), tyvar("b")), arrow(tyvar("a"), tyvar("b")));
    assert_eq!(tycon("A", vec![]), tycon("A", vec![]));
    assert_eq!(tycon("A", vec![tyvar("b")]), tycon("A", vec![tyvar("b")]));
    assert_eq!(tycon("A", vec![tyvar("b"),tyvar("c")]), tycon("A", vec![tyvar("b"),tyvar("c")]));
}

#[test]
fn test_subst_lookup1() {
    // substの羃等性をチェック。置換対象ではない型変数はそのものが返る。
    let subst0 = Subst::empty();
    assert_eq!(subst0.lookup(&tyvar("a")), tyvar("a"));
}

#[test]
fn test_subst_lookup2() {
    // substの羃等性をチェック。置換対象ではない型変数はそのものが返る。
    let subst0 = Subst::empty();
    let subst1 = subst0.clone().extend(tyvar("a"), tyvar("b"));
    assert_eq!(subst0.lookup(&tyvar("a")), tyvar("a"));  // subst0は変化していない
    assert_ne!(subst0, subst1);
    assert_eq!(subst1.lookup(&tyvar("a")), tyvar("b")); // a == b
    assert_eq!(subst1.lookup(&tyvar("b")), tyvar("b")); // b == b
}

#[test]
fn test_subst_call_tyvar1() {
    // substによる2段置換のテスト。
    let subst = Subst::empty()
                .extend(tyvar("b"), tyvar("c")) // b → c
                .extend(tyvar("a"), tyvar("b")) // a → b
                ;
    assert_eq!(subst.call(&tyvar("a")), tyvar("c")); // a (→b) == c
    assert_eq!(subst.call(&tyvar("b")), tyvar("c")); // b == c
    assert_eq!(subst.call(&tyvar("c")), tyvar("c")); // c == c
}

#[test]
fn test_subst_call_tyvar2() {
    // substによる2段置換のテスト。extendの順序を変更しても同じ結果 。
    let subst = Subst::empty()
                .extend(tyvar("a"), tyvar("b")) // a → b
                .extend(tyvar("b"), tyvar("c")) // b → c
                ;
    assert_eq!(subst.call(&tyvar("a")), tyvar("c")); // a (→b) == c
    assert_eq!(subst.call(&tyvar("b")), tyvar("c")); // b == c
    assert_eq!(subst.call(&tyvar("c")), tyvar("c")); // c == c
}

#[test]
fn test_subst_call_tyvar3() {
    // substによる2段置換のテスト。同じ変数に対する置換は、後勝ち。
    let subst0 = Subst::empty()
                .extend(tyvar("a"), Type::Tyvar("x".to_string())) // a → x
                ;
    let subst1 = subst0.clone()
                .extend(tyvar("a"), Type::Tyvar("y".to_string())) // a → y
                ;
    assert_eq!(subst0.call(&tyvar("a")), Type::Tyvar("x".to_string())); // a==x
    assert_eq!(subst1.call(&tyvar("a")), Type::Tyvar("y".to_string())); // a==y
}

#[test]
fn test_subst_call_tyvar4() {   // Ignore me
    // 循環参照のテスト。
    let _subst = Subst::empty()
                .extend(tyvar("a"), tyvar("b")) // a → b
                .extend(tyvar("b"), tyvar("c")) // b → c
                .extend(tyvar("c"), tyvar("a")) // c → a
                ;

    // 循環参照に対応していない(以下をコメントアウトすると無限ループする)。
    // TODO: should avoid infinite loop
    // assert_eq!(subst.call(&tyvar("a")), tyvar("c"));
    // assert_eq!(subst.call(&tyvar("b")), tyvar("c"));
    // assert_eq!(subst.call(&tyvar("c")), tyvar("c"));
}

#[test]
fn test_subst_call_arrow1() {
    // Arrowへの置換
    let subst = Subst::empty()
                .extend(tyvar("a"), arrow(tyvar("b"), tyvar("c"))) // a → (b->c)
                ;
    assert_eq!(subst.lookup(&tyvar("a")), arrow(tyvar("b"), tyvar("c"))); // a  == (b->c)
    assert_eq!(subst.call(&tyvar("a")), arrow(tyvar("b"), tyvar("c"))); // a == (b->c)
}

#[test]
fn test_subst_call_arrow2() {
    // Arrowとtyvarへの両方を含み、置換対象のtyvarをArrowが含む。
    let subst = Subst::empty()
                .extend(tyvar("b"), tyvar("c")) // b→c
                .extend(tyvar("a"), arrow(tyvar("b"), tyvar("c"))) // a → (b->c)
                ;
    assert_eq!(subst.call(&tyvar("a")), arrow(tyvar("c"), tyvar("c"))); // a==(c->c)
    let subst2 = subst.clone().extend(tyvar("d"), tyvar("a"));  // d→a
    assert_eq!(subst2.call(&tyvar("d")), arrow(tyvar("c"), tyvar("c"))); // d==(c->c)
    let subst3 = subst.clone().extend(tyvar("c"), tyvar("d"));  // c→d
    assert_eq!(subst3.call(&tyvar("a")), arrow(tyvar("d"), tyvar("d"))); // a==(d->d)
}

#[test]
fn test_subst_call_tycon1() {
    // 単相型への置換
    let subst = Subst::empty()
                .extend(tyvar("a"), tycon("B", vec![])) // a→B[]
                ;
    assert_eq!(subst.call(&tyvar("a")), tycon("B", vec![])); // a==B[]
}

#[test]
fn test_subst_call_tycon2() { // a→B[c,d]
    // 多相型への置換
    let subst = Subst::empty()
                .extend(tyvar("a"), tycon("B", vec![tyvar("c"),tyvar("d")])) // a→B[c,d]
                ;
    assert_eq!(subst.call(&tyvar("a")), tycon("B", vec![tyvar("c"),tyvar("d")])); // a==B[c,d]
}

#[test]
fn test_subst_call_tycon3() {    // a→B[c,d], b → x,  c → y, d → z
    // 置換の連鎖
    let subst = Subst::empty()
                .extend(tyvar("a"), tycon("B", vec![tyvar("c"), tyvar("d")])) // a → B[c, d]
                .extend(tyvar("b"), tyvar("x")) // b → x
                .extend(tyvar("c"), tyvar("y")) // c → y
                .extend(tyvar("d"), tyvar("z")) // d → z
                ;
    assert_eq!(subst.call(&tyvar("a")), tycon("B", vec![Type::Tyvar("y".to_string()),Type::Tyvar("z".to_string())])); // a==B[c,d]
    // type constructor name 'b' is not substituted.
}

#[test]
fn test_subst_apply_env1() {
    // Envに対する置換。環境に登録されている型スキーマの型変数が(フリーか否かにかかわらず)置換される。
    let subst = Subst::empty();
    let mut env = Env::new();
    assert_eq!(subst.call_env(&env).len(), 0);
    env.insert("x".to_string(), TypeScheme::new(vec![tyvar("a"), tyvar("b")], arrow(tyvar("a"), tyvar("c"))));
    let subst = subst.extend(tyvar("a"), tyvar("b"));
    assert_eq!(env.len(), 1);
    assert_eq!(subst.call_env(&env)["x"].to_string(), "∀ (a,b) . ((b -> c))");
}

#[test]
fn test_type_scheme_new_instance1() {
    // 型スキーマをnewInstance()するときに型変数が置換されることの確認
    TYPEINFER.with(|ti| ti.reset());
    let ts = TypeScheme::new(vec![tyvar("a"), tyvar("b")], tyvar("a"));
    // where 'a' is bounded
    assert_eq!(ts.tyvars, [tyvar("a"), tyvar("b")]);
    assert_eq!(ts.tpe, tyvar("a"));
    assert_eq!(ts.to_string(), "∀ (a,b) . (a)");
    let t1 = ts.new_instance(); // 'a' of ts1.tpe is replaced to 'a0'
    assert_eq!(t1.to_string(), "a0");
}

#[test]
fn test_type_scheme_new_instance2() {
    // 型スキーマをnewInstance()するときにフリー型変数が置換されないことの確認
    TYPEINFER.with(|ti| ti.reset());
    let ts = TypeScheme::new(vec![tyvar("a"), tyvar("b")], tyvar("c")); // where 'c' is a free variable
    assert_eq!(ts.tyvars, [tyvar("a"), tyvar("b")]);
    assert_eq!(ts.tpe, tyvar("c"));
    assert_eq!(ts.to_string(), "∀ (a,b) . (c)");
    let t1 = ts.new_instance(); // a,b is replaced but 'c' of ts.tpe is not changed
    assert_eq!(t1.to_string(), "c");
}

#[test]
fn test_env_new_lookup1() {
    let mut e = Env::new();
    // 識別子に結びつけた型スキーマが環境からlookupできること。
    e.insert("a".to_string(), TypeScheme::new(vec![tyvar("a"), tyvar("b")], tyvar("c")));
    e.insert("b".to_string(), TypeScheme::new(vec![tyvar("a"), tyvar("b")], arrow(tyvar("a"), tyvar("c"))));
    assert_eq!(TypeInfer::lookup(&e, "a".to_string()), Some(&TypeScheme::new(vec![tyvar("a"), tyvar("b")], tyvar("c"))));
    assert_eq!(TypeInfer::lookup(&e, "b".to_string()), Some(&TypeScheme::new(vec![tyvar("a"), tyvar("b")], arrow(tyvar("a"), tyvar("c")))));
    assert_eq!(TypeInfer::lookup(&e, "c".to_string()), None);
}

#[test]
fn test_gen_type1() {
    let e = Env::new();
    // 型に含まれる型変数は全称量化される。
    assert_eq!(TYPEINFER.with(|ti| ti.gen(&e, tyvar("a"))).to_string(), TypeScheme::new(vec![tyvar("a")], tyvar("a")).to_string());
    assert_eq!(TYPEINFER.with(|ti| ti.gen(&e, arrow(tyvar("a"),tyvar("b")))).to_string(), TypeScheme::new(vec![tyvar("a"), tyvar("b")], arrow(tyvar("a"),tyvar("b"))).to_string());
}

#[test]
fn test_gen_type2() {
    let mut e = Env::new();
    e.insert("a".to_string(), TypeScheme::new(vec![tyvar("b"), tyvar("c")], tyvar("a"))); // a is free
    // 型に含まれる型変数は全称量化されるが、
    // この環境に登録されている型スキーマでフリーな変数aは全称量化の対象外となる。
    assert_eq!(TYPEINFER.with(|ti| ti.gen(&e, tyvar("a"))).to_string(), TypeScheme::new(vec![], tyvar("a")).to_string());
    assert_eq!(TYPEINFER.with(|ti| ti.gen(&e, arrow(tyvar("a"),tyvar("b")))).to_string(), TypeScheme::new(vec![tyvar("b")], arrow(tyvar("a"),tyvar("b"))).to_string());
}

#[test]
fn test_new_tyvar1() {
    // 重複しない名前の新しい型変数を作成して返す。
    TYPEINFER.with(|ti| ti.reset());
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a0"));
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a1"));
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a2"));
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a3"));
    TYPEINFER.with(|ti| ti.reset());
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a0"));
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a1"));
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a2"));
    assert_eq!(TYPEINFER.with(|ti| ti.new_tyvar()), tyvar("a3"));
}

#[test]
fn test_tyvars_type1() {
    // // 型に対するtyvars()は指定した型Type t中に含まれる型変数のリストが取得できること。
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars(tyvar("a"))), [tyvar("a")]);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars(arrow(tyvar("a"),tyvar("b")))), [tyvar("a"),tyvar("b")]);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars(tycon("b", vec![tyvar("c"), tyvar("d")]))), [tyvar("c"),tyvar("d")]);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars(arrow(tycon("c",vec![tyvar("a"),tyvar("b")]),
                            tycon("c",vec![tyvar("c"),tyvar("b")])))), [tyvar("a"),tyvar("b"),tyvar("c"),tyvar("b")]);
    // リストなので特に重複を回避していない(元のscala版もそうなっている)
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars(tycon("c",vec![arrow(tyvar("a"),tyvar("b")),
                                    arrow(tyvar("b"),tyvar("c"))]))), [tyvar("a"),tyvar("b"),tyvar("b"),tyvar("c")]);
}

#[test]
fn test_tyvars_typescheme1() {
    // 型スキーマに対するtyvarsは、型本体が使用している型変数から、全
    // 称量化された変数を除外したものを返す。
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_typescheme(TypeScheme::new(vec![], tyvar("a")))), [tyvar("a")]);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_typescheme(TypeScheme::new(vec![tyvar("a")], tyvar("a")))), []);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_typescheme(TypeScheme::new(vec![tyvar("a")], tyvar("c")))), [tyvar("c")]);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_typescheme(TypeScheme::new(vec![tyvar("a")], arrow(tyvar("a"),tyvar("b"))))), [tyvar("b")]);
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_typescheme(TypeScheme::new(vec![tyvar("a")], arrow(tyvar("a"),tyvar("a"))))), []);
}

#[test]
fn test_tyvars_env1() {
    // 環境Envに対するtyvarsは、その環境に登録されているすべての型スキー
    // マに対するtvarsの値全体を返す。
    // つまり、環境全体が含む全称量化に関するフリー変数の集合を返す。
    let mut e = Env::new();
    e.insert("a".to_string(), TypeScheme::new(vec![tyvar("b"), tyvar("c")], tyvar("a"))); // a is free
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_env(&e)), vec![tyvar("a")]);
    e.insert("b".to_string(), TypeScheme::new(vec![tyvar("f"), tyvar("e")], tyvar("d"))); // d is free
    assert_eq!(TYPEINFER.with(|ti| ti.tyvars_env(&e)), vec![tyvar("a"), tyvar("d")]);
}

#[test]
fn test_mgu_tyvar1() { // a <=> a
    // 同じ型変数同士のユニフィケーション(一致する)
    let (left0, right0) = (tyvar("a"), tyvar("a"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1); 
}

#[test]
fn test_mgu_tyvar2() { // a<=>b
    // 異る型変数同士のユニフィケーション。
    // 片一方をもう一方の型変数に一致させることで一致。
    let (left0, right0) = (tyvar("a"), tyvar("b"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap(); // a→b
    let (left1, right1) = (subst.call(&left0), subst.call(&right0)); // (a→)b, b
    assert_eq!(left1, right1); // b==b
}

#[test]
fn test_mgu_arrow1() { // A->B <=> A->B
    // 同じ単相Arrow同士のユニフィケーション。成功する。
    let left0 = arrow(tycon("A",vec![]), tycon("B",vec![]));
    let right0 = arrow(tycon("A",vec![]), tycon("B",vec![]));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
}

#[test]
fn test_mgu_arrow2() { // A->B <=> A->C
    // 異る型の単相Arrow同士のユニフィケーション。失敗する。
    let left0 = arrow(tycon("A",vec![]), tycon("B",vec![]));
    let right0 = arrow(tycon("A",vec![]), tycon("C",vec![]));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify C[] with B[]");
}

#[test]
fn test_mgu_arrow_p1() { // a->b <=> c->d
    // 多相Arrow同士のユニフィケーション。成功する。
    let left0 = arrow(tyvar("a"), tyvar("b"));
    let right0 = arrow(tyvar("c"), tyvar("d"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
}

#[test]
fn test_mgu_arrow_p2() { // A->B <=> A->c
    // 単相Arrowと多相Arrowのユニフィケーション。成功する。
    let left0 = arrow(tycon("A",vec![]), tycon("B",vec![]));
    let right0 = arrow(tycon("A",vec![]), tyvar("c"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
    assert_eq!(right1, arrow(tycon("A",vec![]), tycon("B",vec![])));
}

#[test]
fn test_mgu_arrow_p3() { // a->B <=> C->d
    // 単相Arrowと多相Arrowのユニフィケーション。成功する。
    let left0 = arrow(tyvar("a"), tycon("B",vec![]));
    let right0 = arrow(tycon("C",vec![]), tyvar("d"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
    assert_eq!(left1, arrow(tycon("C",vec![]), tycon("B",vec![])));
    assert_eq!(right1, arrow(tycon("C",vec![]), tycon("B",vec![])));
}

#[test]
fn test_mgu_tycon1() { // A[] <=> A[]
    // 同じ単相型コンストラクタ同士のユニフィケーション(一致する)
    let (left0, right0) = (tycon("A",vec![]), tycon("A",vec![]));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
}

#[test]
fn test_mgu_tycon2() { // A[] <=> B[]
    // 異なる単相型コンストラクタ同士のユニフィケーション。
    // 一致する置換はないので型エラー。
    let (left0, right0) = (tycon("A",vec![]), tycon("B",vec![]));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify A[] with B[]");
}

#[test]
fn test_mgu_tycon3() { // A[AA] <=> A[]
    // 異なる単相型コンストラクタ同士(引数の個数が異なる)のユニフィケーション。 
    // 一致する置換はないので型エラー。
    // unify A[AA] and A[]. it fails because there is no valid substitution.
    let (left0, right0) = (tycon("A",vec![tycon("AA",vec![])]), tycon("A",vec![]));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify [AA[]] with [], number of type arguments are different");
}

#[test]
fn test_mgu_tycon4() { // A[AA] <=> A[AB]
    // 異なる単相型コンストラクタ同士(引数の値が異なる)のユニフィケーション。
    // 一致する置換はないので型エラー。
    // unify A[AA] and A[AB]. it fails because there is no valid substitution.
    let (left0, right0) = (tycon("A",vec![tycon("AA",vec![])]), tycon("A",vec![tycon("AB",vec![])]));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify AA[] with AB[]");
}

#[test]
fn test_mgu_tycon_p1() { // A[a] <=> A[a]
    // 同じ多相型コンストラクタ同士のユニフィケーション(一致する)
    // unify A[a] and A[a]. success (trivial).
    let (left0, right0) = (tycon("A",vec![tyvar("a")]), tycon("A",vec![tyvar("a")]));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
}

#[test]
fn test_mgu_tycon_p2() { // A[a] <=> A[b]
    // 引数が異なる型変数の多相型コンストラクタ同士のユニフィケーション。
    // 型変数同士のmguによって一致する。(b=a)
    // unify A[a] and A[b]. success with substitiution of b->a (or a->b)
    let (left0, right0) = (tycon("A",vec![tyvar("a")]), tycon("A",vec![tyvar("b")]));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
}

#[test]
fn test_mgu_tycon_p3() { // A[a] <=> A[] (TypeError!)
    // 異なる多相型コンストラクタ同士(引数の個数が異なる)のユニフィケーション。
    // 一致する置換はないので型エラー。
    // unify A[a] and A[]. it fails because there is no valid substitution.
    let (left0, right0) = (tycon("A",vec![tyvar("a")]), tycon("A",vec![]));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify [a] with [], number of type arguments are different");
}

#[test]
fn test_mgu_tycon_p4() { // A[a] <=> B[a] (TypeError!)
    // 異なる多相型コンストラクタ同士(引数の値が異なる)のユニフィケーション。
    // 一致する置換はないので型エラー。
    // unify A[a] and B[a]. it fails because there is no valid substitution.
    let (left0, right0) = (tycon("A",vec![tyvar("a")]), tycon("B",vec![tyvar("a")]));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify A[a] with B[a]");
}

#[test]
fn test_mgu_tyvar_arrow1() { // a <=> B->C
    // 型変数aと関数型B->Cのユニフィケーション。成功する(a=B->C)
    // unify type variable a and functional type B->C. succeed with a=B->C
    let (left0, right0) = (tyvar("a"), arrow(tycon("B",vec![]), tycon("C",vec![])));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
    assert_eq!(left1, arrow(tycon("B",vec![]), tycon("C",vec![])));
}

#[test]
fn test_mgu_tyvar_arrow2() { // B->C <=> a
    // 関数型B->Cと型変数aのユニフィケーション。成功する(a=B->C)。
    // unify functional type B->C and type variable a. succeed with a=B->C
    let (left0, right0) = (arrow(tycon("B",vec![]), tycon("C",vec![])), tyvar("a"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
    assert_eq!(right1, arrow(tycon("B",vec![]), tycon("C",vec![])));
}

#[test]
fn test_mgu_tyvar_tycon1() { // a <=> B
    // 型変数aと型コンストラクタB[]のユニフィケーション。成功する(a=B[])
    // unify type variable a and type constructor B[]. succeed with a=B[]
    let (left0, right0) = (tyvar("a"), tycon("B",vec![]));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
    assert_eq!(left1, tycon("B",vec![]));
}

#[test]
fn test_mgu_tyvar_tycon2() { // B <=> a
    // 型コンストラクタB[]と型変数aのユニフィケーション。成功する(a=B[])。
    // unify type constructor B[] and type variable a. succeed with a=B[]
    let (left0, right0) = (tycon("B",vec![]), tyvar("a"));
    let subst = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap();
    let (left1, right1) = (subst.call(&left0), subst.call(&right0));
    assert_eq!(left1, right1);
    assert_eq!(right1, tycon("B",vec![]));
}

#[test]
fn test_mgu_tycon_arrow1() { // A <=> a->b (TypeError!)
    // 型コンストラクタとArrowのユニフィケーション。失敗する。
    // unify type constructor and arrow. it fails.
    let (left0, right0) = (tycon("A",vec![]), arrow(tyvar("a"), tyvar("b")));
    let TypeError(msg) = TYPEINFER.with(|ti| ti.mgu(&left0, &right0, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify A[] with (a -> b)");
}

// void testZip() {
//     assert TypeInfer.zip([1,2,3],["a","b","c"]) == [[1,"a"],[2,"b"],[3,"c"]]
//     assert TypeInfer.zip([],[]) == []
//     shouldFail (TypeError) { TypeInfer.zip([1,2],["a","b","c"]) == [[1,"a"],[2,"b"],[3,"c"]] }
// }
#[test]
fn test_mgu_zip() {
    assert_eq!(TypeInfer::zip(vec![1,2,3],vec!["a","b","c"]).unwrap(), [(1,"a"),(2,"b"),(3,"c")]);
    assert_eq!(TypeInfer::zip(vec![] as Vec<i8>,vec![] as Vec<i8>).unwrap(), vec![]);
    assert_eq!(TypeInfer::zip(vec![1,2],vec!["a","b","c"]).unwrap_err(), TypeError("cannot unify [1,2] with [a,b,c], number of type arguments are different".to_string()));
}

#[test]
fn test_tp_var1() { // [a:A] |- a : A
    let mut env = Env::new();
    env.insert("a".to_string(), TypeScheme::new(vec![], tycon("A",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &var("a"), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("A", vec![]));
}

#[test]
fn test_tp_var2() { // [] |- a : TypeError!
    let env = Env::new();
    let typ = tyvar("a");
    let TypeError(msg) = TYPEINFER.with(|ti| ti.tp(&env, &var("a"), &typ, Subst::empty())).unwrap_err();
    assert_eq!(msg, "undefined: a");
}

#[test]
fn test_tp_lam1() { // [1:Int] |- (\a -> a) 1 : Int
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &app(lam("a", var("a")), var("1")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_lam2() { // [true:Bool, 1:Int] |- (\a -> true) 1 : Bool
    let mut env = Env::new();
    env.insert("true".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &app(lam("a", var("true")), var("1")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Boolean", vec![]));
}

#[test]
fn test_tp_lam3() { // [1:Int, a:Bool] |- (\a -> a) 1 : Int
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    env.insert("a".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &app(lam("a", var("a")), var("1")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_lam4() { // [add:Int->(Int->Int),1:Int] |- add(1)1) : Int
    let mut env = Env::new();
    env.insert("add".to_string(), TypeScheme::new(vec![], arrow(tycon("Int",vec![]), arrow(tycon("Int",vec![]),tycon("Int",vec![])))));
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &app(app(var("add"), var("1")), var("1")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_let1() { // [1:Int] |- let a = 1 in a : Int
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &let_("a", var("1"), var("a")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_let2() { // [true:Bool, 1:Int] |- let a = 1 in true : Bool
    let mut env = Env::new();
    env.insert("true".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &let_("a", var("1"), var("true")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Boolean", vec![]));
}

#[test]
fn test_tp_let3() { // [1:Int, a:Bool] |- let a = 1 in a : Int
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    env.insert("a".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &let_("a", var("1"), var("a")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_let4() { // [1:Int] |- let a = a in 1 : (TypeError!)
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let TypeError(msg) = TYPEINFER.with(|ti| ti.tp(&env, &let_("a", var("a"), var("1")), &typ, Subst::empty())).unwrap_err();
    assert_eq!(msg, "undefined: a");
}

#[test]
fn test_tp_lam_let1() {
    //  [e1:Bool, 1:Int] |- (\ x -> let y=e1 in x) 1 : Int
    //
    // 「 \ x -> let y=e1 in x」のように、λ本体の中にlet式が出現す
    // るときに、let束縛される識別子yのために登録される型スキーマで
    // は、xに対応する型スキーマで使用されている型変数が全称限量対
    // 象から除外される。
    let mut env = Env::new();
    env.insert("e1".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, 
                                            &app(
                                                lam("x",
                                                    let_("y", var("e1"), var("x"))),
                                                var("1")
                                            ), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_lam_p1() {
    //  [s:String, 7:Int] |- (\ x -> x s) (\x->7) : Int
    // λ変数xに多相関数を束縛し、x->Intでインスタンス化する。
    // bind lambda variable x to polymorphic function and instantiate with x->Int type.
    let mut env = Env::new();
    env.insert("s".to_string(), TypeScheme::new(vec![], tycon("String",vec![])));
    env.insert("7".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, 
                                &app(
                                    lam("x",
                                        app(var("x"), var("s"))),
                                    lam("x", var("7"))
                                ),
                                &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_lam_p2() {
    //  [s:String, c:Char, 7:Int, add:Int->(Int->Int)] |- (\ x -> (add(x s))(x c)) (\x->7) : TypeError!
    //  λ変数xが多相関数(a->Int)のとき、異なる型での複数回のインスタンス化でエラーになることの確認。
    //  if the lambda variable x is polymorphic function(a->Int), it should be error
    //  every type instantiation for each different type occurence of x.
    let mut env = Env::new();
    env.insert("add".to_string(), TypeScheme::new(vec![], arrow(tycon("Int",vec![]), arrow(tycon("Int",vec![]),tycon("Int",vec![])))));
    env.insert("c".to_string(), TypeScheme::new(vec![], tycon("Char",vec![])));
    env.insert("s".to_string(), TypeScheme::new(vec![], tycon("String",vec![])));
    env.insert("7".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let TypeError(msg) = TYPEINFER.with(|ti| ti.tp(&env, 
                                &app(
                                    lam("x",
                                        app(
                                            app(var("add"),
                                                app(var("x"), var("s"))),
                                            app(var("x"), var("c")))
                                        ),
                                    lam("x", var("7"))
                                ),
                                &typ, Subst::empty())).unwrap_err();
    assert_eq!(msg, "cannot unify Char[] with String[]");
}

#[test]
fn test_tp_let_p1() {
    //  [s:String, c:Char, 7:Int, add:Int->(Int->Int)] |- (let x=(\x->7) in (add(x s))(x c)) : Int
    //  let変数xが多相関数(a->Int)のとき、異なる型での複数回のインスタンス化でエラーにならないことの確認。
    //  if the let variable x is polymorphic function(a->Int), it should not be error
    //  every type instantiation for each different type occurence of x.
    let mut env = Env::new();
    env.insert("add".to_string(), TypeScheme::new(vec![], arrow(tycon("Int",vec![]), arrow(tycon("Int",vec![]),tycon("Int",vec![])))));
    env.insert("c".to_string(), TypeScheme::new(vec![], tycon("Char",vec![])));
    env.insert("s".to_string(), TypeScheme::new(vec![], tycon("String",vec![])));
    env.insert("7".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, 
                                &let_("x",
                                    lam("x", var("7")),
                                    app(
                                        app(var("add"),
                                            app(var("x"), var("s"))),
                                        app(var("x"), var("c")))
                                ),
                                &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_letrec1() { // [1:Int] |- letrec a = 1 in a : Int
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &letrec("a", var("1"), var("a")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_letrec2() { // [true:Bool, 1:Int] |- letrec a = 1 in true : Bool
    let mut env = Env::new();
    env.insert("true".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &letrec("a", var("1"), var("true")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Boolean", vec![]));
}

#[test]
fn test_tp_letrec3() { // [true:Bool, 1:Int] |- letrec a = 1 in true : Bool
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    env.insert("a".to_string(), TypeScheme::new(vec![], tycon("Boolean",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &letrec("a", var("1"), var("a")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_letrec_p1() {
    //  [s:String, c:Char, 7:Int, add:Int->(Int->Int)] |- (letrec x=(\x->7) in (add(x s))(x c)) : Int
    //  letrec変数xが多相関数(a->Int)のとき、異なる型での複数回のインスタンス化でエラー
    //  にならないことの確認。
    //  if the letrec variable x is polymorphic function(a->Int), it should not be error
    //  every type instantiation for each different type occurence of x.
    let mut env = Env::new();
    env.insert("add".to_string(), TypeScheme::new(vec![], arrow(tycon("Int",vec![]), arrow(tycon("Int",vec![]),tycon("Int",vec![])))));
    env.insert("c".to_string(), TypeScheme::new(vec![], tycon("Char",vec![])));
    env.insert("s".to_string(), TypeScheme::new(vec![], tycon("String",vec![])));
    env.insert("7".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, 
                                &letrec("x",
                                    lam("x", var("7")),
                                    app(
                                        app(var("add"),
                                            app(var("x"), var("s"))),
                                        app(var("x"), var("c")))
                                ),
                                &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_tp_letrec4() { // [1:Int] |- letrec a = a in 1 : Int
    let mut env = Env::new();
    env.insert("1".to_string(), TypeScheme::new(vec![], tycon("Int",vec![])));
    let typ = tyvar("a");
    let subst = TYPEINFER.with(|ti| ti.tp(&env, &letrec("a", var("a"), var("1")), &typ, Subst::empty())).unwrap();
    assert_eq!(subst.call(&typ), tycon("Int", vec![]));
}

#[test]
fn test_typeof() { // [] |- (\a->a) : a->a
    let env = Env::new();
    let typ = TYPEINFER.with(|ti| ti.type_of(&env, &lam("a", var("a")))).unwrap();
    assert!(match &typ {&Type::Arrow(ref t1,ref t2) => t1 == t2, _ => false });
}

#[test]
fn test_predefined_env() {
    let env = TYPEINFER.with(|ti| ti.predefined_env());
    let typ = TYPEINFER.with(|ti| ti.type_of(&env, &var("true"))).unwrap();
    assert_eq!(typ, tycon("Boolean", vec![]));
}

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
