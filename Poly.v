(** * Poly: Polymorphism and Higher-Order Functions *)

(* Final reminder: Please do not put solutions to the exercises in
   publicly accessible places.  Thank you!! *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

(* ################################################################# *)
(** * Polymorphism *)

(** 在本章中，我们会继续发展函数式编程的基本概念，其中最关键的新概念就是 多态
   （在所处理的数据类型上抽象出函数）和高阶函数（函数作为数据）。 *)

(* ================================================================= *)
(** ** Polymorphic Lists *)

(** 在前几章中，我们只是使用了数的列表。很明显，有趣的程序还需要能够处理其它元素类型的列表，
    如字符串列表、布尔值列表、 列表的列表等等。我们可以分别为它们定义新的归纳数据类型，例如...*)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(** ...不过这样很快就会变得乏味。 部分原因在于我们必须为每种数据类型都定义不同的构造子， 
    然而主因还是我们必须为每种数据类型再重新定义一遍所有的列表处理函数 （如 length、rev 等）。*)

(** 为避免这些重复，Coq 支持定义多态归纳类型。 例如，以下就是多态列表数据类型。 *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** 这和上一章中 [natlist] 的定义基本一样，只是将 [cons] 构造子的 [nat] 参数换成了任意的类型
     [X]，定义的头部添加了 [X] 的绑定， 而构造子类型中的 [natlist] 则换成了 [list X]。（我们
     可以重用构造子名 [nil] 和 [cons]，因为之前定义的 [natlist] 在当前作用之外的一个
      [Module] 中。）

      [list] 本身又是什么类型？一种不错的思路就是把 [list] 当做从 [Type] 类型到 [Inductive] 
      归纳定义的函数；或者换种思路，即 [list] 是个从 [Type] 类型到 [Type] 类型的函数。对于任何
      特定的类型 [X]， 类型 [list X] 是一个 [Inductive] 归纳定义的，元素类型为 [X] 的列表的
      集合。 *)

Check list.
(* ===> list : Type -> Type *)

(** The parameter [X] in the definition of [list] automatically
    becomes a parameter to the constructors [nil] and [cons] -- that
    is, [nil] and [cons] are now polymorphic constructors; when we use
    them, we must now provide a first argument that is the type of the
    list they are building. For example, [nil nat] constructs the
    empty list of type [nat]. *)

Check (nil nat).
(* ===> nil nat : list nat *)

(** [cons nat] 与此类似，它将类型为 [nat] 的元素添加到类型为 [list nat] 的列表中。
    以下示例构造了一个只包含自然数 3 的列表： *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(** [nil] 的类型可能是什么？我们可以从定义中看到 [list X] 的类型， 它忽略了 [list] 的
    形参 [X] 的绑定。[Type → list X] 并没有解释 [X] 的含义，[(X : Type) → list X] 则
    比较接近。Coq 对这种情况的记法为 [forall X : Type, list X]. *)

Check nil.
(* ===> nil : forall X : Type, list X *)

(** 类似地，定义中 [cons] 看起来像 [X → list X → list X] 然而以此约定来解释
    [X] 的含义则是类型 [forall X, X → list X → list X]. *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** （关于记法的附注：在 .v 文件中，量词 "forall" 会写成字母的形式， 而在生成的
     HTML 和一些设置了显示控制的 IDE 中，[forall] 通常会渲染成一般的 "∀" 数学符号，
     虽然你偶尔还是会看到英文拼写的 "forall"。这只是排版上的效果，它们的含义没有任何区别。）*)

(** 如果在每次使用列表构造子时，都要为它提供类型参数，那样会很麻烦。 不过我们很快
    就会看到如何省去这种麻烦。 *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** （这里显式地写出了 [nil] 和 [cons]，因为我们还没为新版本的列表定义 [[]] 和 [::] 记法。
      我们待会儿再干。)
      现在我们可以回过头来定义之前写下的列表处理函数的多态版本了。 例如 [repeat]： *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** 同 [nil] 与 [cons] 一样，我们可以通过将 [repeat] 应用到一个类型、
    一个该类型的元素以及一个数字来使用它：*)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(** 要用 [repeat] 构造其它种类的列表， 我们只需通过对应类型的参数将它实例化即可：*)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.


(** **** Exercise: 2 stars, standard (mumble_grumble)  

    Consider the following two inductively defined types. *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)] "NO"
      - [d mumble (b a 5)] "YES"
      - [d bool (b a 5)] "YES"
      - [e bool true] "YES"
      - [e mumble (b c 0)] "NO"
      - [e bool (b c 0)] "NO"
      - [c] "YES" *)
(* FILL IN HERE *)
Eval compute in d mumble (b a 5).
Eval compute in d bool (b a 5).
Eval compute in e bool true.
Eval compute in c.
End MumbleGrumble.

(* Do not modify the following line: *)
Definition manual_grade_for_mumble_grumble : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Type Annotation Inference *)

(** 我们再写一遍 [repeat] 的定义，不过这次不指定任何参数的类型。 Coq 还会接受它么？ *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** I当然会。我们来看看 Coq 赋予了 [repeat'] 什么类型： *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(** 它与 [repeat] 的类型完全一致。Coq 可以使用类型推断 基于它们的使用方式来推出 [X]、[x] 
    和 [count] 一定是什么类型。例如， 由于 [X] 是作为 [cons] 的参数使用的，因此它必定是个
    [Type] 类型， 因为 [cons] 期望一个 [Type] 作为其第一个参数，而用 [0] 和 [S] 来匹配
     [count] 意味着它必须是个 [nat]，诸如此类。

    这种强大的功能意味着我们不必总是在任何地方都显式地写出类型标注， 不过显式的类型标注对于
    文档和完整性检查来说仍然非常有用， 因此我们仍会继续使用它。你应当在代码中把握好使用
    类型标注的平衡点， 太多导致混乱并分散注意力，太少则会迫使读者为理解你的代码
    而在大脑中进行类型推断。*)

(* ----------------------------------------------------------------- *)
(** *** Type Argument Synthesis *)

(** 要使用多态函数，我们需要为其参数再额外传入一个或更多类型。 例如，前面 [repeat]
    函数体中的递归调用必须传递类型 [X]。不过由于 [repeat] 的第二个参数为 [X] 类型
    的元素，第一个参数明显只能是 X， 既然如此，我们何必显式地写出它呢？

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write a "hole" [_], which can be
    read as "Please try to figure out for yourself what belongs here."
    More precisely, when Coq encounters a [_], it will attempt to
    _unify_ all locally available information -- the type of the
    function being applied, the types of the other arguments, and the
    type expected by the context in which the application appears --
    to determine what concrete type should replace the [_].

    这听起来很像类型标注推断。实际上，这两种个过程依赖于同样的底层机制。 
    除了简单地忽略函数中某些参数的类型：

      repeat' X x count : list X :=

    我们还可以将类型换成 [_]：

      repeat' (X : _) (x : _) (count : _) : list X :=

    以此来告诉 Coq 要尝试推断出缺少的信息。

    Using holes, the [repeat] function can be written like this: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** 在此例中，我们写出 [_] 并没有省略多少 [X]。然而在很多情况下，
    这对减少击键次数和提高可读性还是很有效的。例如，假设我们要写下
    一个包含数字 1、2 和 3 的列表，此时不必写成这样： *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use holes to write this: *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

(** 我们甚至可以通过告诉 Coq 总是推断给定函数的类型参数来避免 [_]。

    [Arguments] 用于指令指定函数或构造子的名字并列出其参数名， 花括号中的
    任何参数都会被视作隐式参数。（如果定义中的某个参数没有名字， 那么它可以
    用通配模式 [_] 来标记。这种情况常见于构造子中。 *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** 现在我们再也不必提供类型参数了： *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** 此外，我们还可以在定义函数时声明隐式参数， 只是需要将它放在花括号内而非圆括号中。例如： *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** (注意我们现在甚至不必在 [repeat'''] 的递归调用中提供类型参数了，
    实际上提供了反而是无效的！)

    我们会尽可能使用最后一种风格，不过还会继续在 Inductive 构造子中
    使用显式的 Argument 声明。原因在于如果将归纳类型的形参标为隐式的话，
    不仅构造子的类型会变成隐式的，类型本身也会变成隐式的。例如， 考虑
    以下 list 类型的另一种定义：*)

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

(** 由于 [X] 在包括 [list'] 本身的整个归纳定义中都是隐式声明的，
    因此当我们讨论数值、布尔值或其它任何类型的列表时，都只能写 [list']，
    而写不了 [list' nat]、[list' bool] 或其它的了，这样就跑得有点太远了。 *)

(** 作为本节的收尾，我们为新的多态列表重新实现几个其它的标准列表函数... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. simpl. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(** 用 [Implicit] 将参数声明为隐式的会有个小问题：Coq 偶尔会没有足够的
    局部信息来确定类型参数。此时，我们需要告诉 Coq 这次我们会显示地给出参数。
    例如，假设我们写了如下定义：*)

Fail Definition mynil := nil.

(** （[Definition] 前面的 [Fail] 限定符可用于 _任何_ 指令， 它的作用是确保该指令
    在执行时确实会失败。如果该指令失败了，Coq 就会打印出相应的错误信息，不过之后会
    继续处理文件中剩下的部分。）

    在这里，Coq 给出了一条错误信息，因为它不知道应该为 [nil] 提供何种类型。 我们
    可以为它提供个显式的类型声明来帮助它，这样 Coq 在"应用" [nil] 时就有更多可用的信息了：*)

Definition mynil : list nat := nil.

(** 此外，我们还可以在函数名前加上前缀 [@] 来强制将隐式参数变成显式的：*)

Check @nil.

Definition mynil' := @nil nat.

(** 使用参数推断和隐式参数，我们可以为列表定义和前面一样的简便记法。
    由于我们让构造子的的类型参数变成了隐式的，因此 Coq 就知道在我们
    使用该记法时自动推断它们了。
 *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** 现在列表就能写成我们希望的方式了： *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard, optional (poly_exercises)  

    Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| n l'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l as [| n1 l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1 as [| n2 l2' IHl2'].
  - reflexivity.
  - simpl. rewrite -> IHl2'. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (more_poly_exercises)  

    Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| n l' IHl'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl'. rewrite -> app_assoc. reflexivity. Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| n l'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Pairs *)

(** 按照相同的模式，我们在上一章中给出的数值序对的定义可被推广为_多态序对_（Polymorphic
    Pairs），它通常叫做_积_（Products）：*)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

(** 和列表一样，我们也可以将类型参数定义成隐式的， 并以此定义类似的具体记法：*)

Notation "( x , y )" := (pair x y).

(** 我们也可以使用 [Notation] 来定义标准的_积类型_（Product Types）记法：*)

Notation "X * Y" := (prod X Y) : type_scope.

(** （标注 [: type_scope] 会告诉 Coq 该缩写只能在解析类型时使用。
    这避免了与乘法符号的冲突。)*)

(** 一开始会很容易混淆 [(x,y)] 和 [X*Y]。不过要记住 [(x,y)] 是一个值，
    它由两个其它的值构造得来；而 [X*Y] 是一个类型， 它由两个其它的类型
    构造得来。如果 [x] 的类型为 [X] 而 [y] 的类型为 [Y]， 那么 [(x,y)]
    的类型就是 [X*Y]。*)

(** 第一元（first）和第二元（second）的射影函数（Projection Functions）
    现在看起来和其它函数式编程语言中的很像了：*)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** 以下函数接受两个列表，并将它们结合成一个序对的列表。 在其它函数式语言中，
    它通常被称作 [zip]。我们为了与 Coq 的标准库保持一致， 将它命名为 [combine]。*)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Exercise: 1 star, standard, optional (combine_checks)  

    Try answering the following questions on paper and
    checking your answers in Coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does

        Compute (combine [1;2] [false;false;true;true]).

      print? 

    [] *)
Check @combine.
(* forall X Y : Type, list X -> list Y -> list (X * Y) *)
Compute (combine [1;2] [false;false;true;true]).
(* [(1, false); (2, false)] *)
(* forall X Y : Type, list X -> list Y -> list (X * Y) *)
(** **** Exercise: 2 stars, standard, recommended (split)  

    The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
    | [] => ([], [])
    | (x, y)::l' => (x::(fst (split l')), y::(snd (split l')))
 end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Options *)

(** One last polymorphic type for now: _polymorphic options_,
    which generalize [natoption] from the previous chapter.  (We put
    the definition inside a module because the standard library
    already defines [option] and it's this one that we want to use
    below.) *)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(** We can now rewrite the [nth_error] function so that it works
    with any type of lists. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, standard, optional (hd_error_poly)  

    Complete the definition of a polymorphic version of the
    [hd_error] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_error {X : Type} (l : list X) : option X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Functions as Data *)

(** Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc. *)

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** Filter *)

(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** Anonymous Functions *)

(** It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

(** Here is the [filter] example, rewritten to use an anonymous
    function. *)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard (filter_even_gt7)  

    Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (partition)  

    Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 3 stars, standard (map_rev)  

    Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, recommended (flat_map)  

    The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** Lists are not the only inductive type for which [map] makes sense.
    Here is a [map] for the [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 2 stars, standard, optional (implicit_args)  

    The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)

    [] *)

(* ================================================================= *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,

       fold plus [1;2;3;4] 0

    yields

       1 + (2 + (3 + (4 + 0))).

    Some more examples: *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, advanced (fold_types_different)  

    Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_fold_types_different : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Functions That Construct Functions *)

(** Most of the higher-order functions we have talked about so
    far take functions as arguments.  Let's look at some examples that
    involve _returning_ functions as the results of other functions.
    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ################################################################# *)
(** * Additional Exercises *)

Module Exercises.

(** **** Exercise: 2 stars, standard (fold_length)  

    Many common functions on lists can be implemented in terms of
    [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length].  (Hint: It may help to
    know that [reflexivity] simplifies expressions a bit more
    aggressively than [simpl] does -- i.e., you may find yourself in a
    situation where [simpl] does nothing but [reflexivity] solves the
    goal.) *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_map)  

    We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it.  (Hint: again, remember that
   [reflexivity] simplifies expressions a bit more aggressively than
   [simpl].) *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_fold_map : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, advanced (currying)  

    In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** As a (trivial) example of the usefulness of currying, we can use it
    to shorten one of the examples that we saw above: *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** Thought exercise: before running the following commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]? *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced (nth_error_informal)  

    Recall the definition of the [nth_error] function:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error l' (pred n)
     end.

   Write an informal proof of the following theorem:

   forall X n l, length l = n -> @nth_error X l n = None
*)
(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** The following exercises explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church.  We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)

Definition three : cnat := @doit3times.

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** **** Exercise: 1 star, advanced (church_succ)  *)

(** Successor of a natural number: given a Church numeral [n],
    the successor [succ n] is a function that iterates its
    argument once more than [n]. *)
Definition succ (n : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, advanced (church_plus)  *)

(** Addition of two natural numbers: *)
Definition plus (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, advanced (church_mult)  *)

(** Multiplication: *)
Definition mult (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, advanced (church_exp)  *)

(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type.  Iterating over [cnat] itself is usually problematic.) *)

Definition exp (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

End Church.

End Exercises.


(* Wed Jan 9 12:02:44 EST 2019 *)
