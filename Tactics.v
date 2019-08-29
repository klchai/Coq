(** * Tactics: More Basic Tactics *)

(** This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.  We will see:

    - how to use auxiliary lemmas in both "forward-style" and
      "backward-style" proofs;
    - how to reason about data constructors (in particular, how to use
      the fact that they are injective and disjoint);
    - how to strengthen an induction hypothesis (and when such
      strengthening is required); and
    - more details on how to reason by case analysis. *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.

(* ################################################################# *)
(** * The [apply] Tactic *)

(** 我们经常会遇到待证目标与上下文中的前提或已证引理刚好_相同_的情况。*)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(** 我们可以像之前那样用"rewrite → eq2. reflexivity."来完成。
    不过如果我们使用 [apply] 策略，只需一步就能达到同样的效果： *)

  apply eq2.  Qed.

(** [apply] 策略也可以配合条件（Conditional）假设和引理来使用：
    如果被应用的语句是一个蕴含式，那么该蕴含式的前提就会被添加到
    待证子目标列表中。*)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** 通常，当我们使用 [apply H] 时，语句 [H] 会以一个绑定了某些 通用变量
    （Universal Variables） 的 [∀] 开始。在 Coq 针对 [H] 的结论匹配当前
    目标时，它会尝试为这些变量查找适当的值。例如， 当我们在以下证明中执行
    [apply eq2] 时，[eq2] 中的通用变量 [q] 会以 [n] 实例化，
    而 [r] 会以 [m] 实例化.*)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, standard, optional (silly_ex)  

    Complete the following proof without using [simpl]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof. intros. apply H0. Qed.
(** [] *)

(** 要使用 [apply] 策略，被应用的事实（的结论）必须精确地匹配证明目标：
    例如, 当等式的左右两边互换后，apply 就无法起效了。 *)

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.

(** 在这里，我们无法直接使用 [apply]，不过我们可以用 [symmetry] 策略
    它会交换证明目标中等式的左右两边。*)

  symmetry.
  simpl. (** (This [simpl] is optional, since [apply] will perform
             simplification first, if needed.) *)
  apply H.  Qed.

(** **** Exercise: 3 stars, standard (apply_exercise1)  

    (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros. rewrite H. symmetry. apply rev_involutive. Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (apply_rewrite)  

    Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied? *)

(* FILL IN HERE 

    [] *)

(* ################################################################# *)
(** * The [apply with] Tactic *)

(** 以下愚蠢的例子在一行中使用了两次改写来将 [a;b] 变成 [e;f]。 *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** 由于这种模式十分常见，因此我们希望一劳永逸地把它作为一条引理记录下来，
    即等式具有传递性。*)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** 现在，按理说我们应该可以用 [trans_eq] 来证明前面的例子了。
    然而，为此我们还需要稍微改进一下 [apply] 策略 *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

(** 如果此时我们只是告诉 Coq [apply trans_eq]，那么它会 （根据该引理的结论对证明目标的匹配）
    说 X 应当实例化为 [[nat]]、[n] 实例化为 [[a,b]]、以及 [o] 实例化为 [[e,f]]。然而，匹配过程并没有为
    [m]确定实例：我们必须在 [apply] 的调用后面加上 [with (m:=[c,d])] 来显式地提供一个实例 *)

  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

(** 实际上，我们通常不必在 [with] 从句中包含名字 [m]，Coq 一般足够聪明来确定我们给出的实例。
    我们也可以写成： [apply trans_eq with [c;d]]。*)

(** **** Exercise: 3 stars, standard, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros. symmetry in H0. rewrite H in H0. rewrite H0. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

(** 回想自然数的定义：

     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

    我们可从该定义中观察到，所有的数都是两种形式之一：要么是构造子 [O]， 要么就是
    将构造子 [S] 应用到另一个数上。

    不过这里还有无法直接看到的： 自然数的定义（以及我们对其它编程语言中数据类型声明
    的工作方式的非形式化理解）中还蕴含了两个事实:

    - 构造子 [S] 是单射（Injective）的。 如果 [S n = S m]，那么 [n = m] 必定成立。

    - 构造子 [O] 和 [S] 是不相交（Disjoint）的。 对于任何 [n] ，[O] 都
    不等于 [S n]。

    类似的原理同样适用于所有归纳定义的类型：所有构造子都是单射的， 而不同构造子构造出
    的值绝不可能相等。对于列表来说，[cons] 构造子是单射的， 而 [nil] 不同于任何
    非空列表。对于布尔值来说，[true] 和 [false] 是不同的。 因为 true 和 false二者
    都不接受任何参数，它们的单射性并不有趣。 其它归纳类型亦是如此 *)

(** 例如，我们可以使用定义在 [Basics.v] 中的 [pred] 函数来证明 S 的单射性。*)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

(** 这个技巧可以通过编写构造子的等价的 [pred] 来推广到任意的构造子上 —— 即编写一个
    "撤销" 一次构造子调用的函数。 作为一种更加简便的替代品， Coq提供了叫做[injection]
    的策略来让我们利用任意构造子的单射性。 此处是使用[injection]对上面定理的另一种证法。*)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** 通过在此处编写 [injection H] ， 我们命令Coq使用构造子的单射性来产生所有它能从
    [H]所推出的等式。 每一个产生的等式都作为一个前件附加在目标上。 
    在这个例子中，附加了前件 [n = m] 。 *)

  injection H. intros Hnm. apply Hnm.
Qed.

(** 此处展示了一个 injection 如何直接得出多个等式的有趣例子。*)

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(** injection 的 "as" 变体允许我们而非Coq来为引入的等式选择名称。 *)

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. Qed.

(** **** Exercise: 1 star, standard (injection_ex3)  *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H0 H1. injection H1. intros _ H2. 
  symmetry. apply H2. Qed.
(** [] *)

(** So much for injectivity of constructors.  What about disjointness?

    The principle of disjointness says that two terms beginning with
    different constructors (like [O] and [S], or [true] and [false])
    can never be equal.  This means that, any time we find ourselves
    working in a context where we've _assumed_ that two such terms are
    equal, we are justified in concluding anything we want to (because
    the assumption is nonsensical).

    The [discriminate] tactic embodies this principle: It is used on a
    hypothesis involving an equality between different
    constructors (e.g., [S n = O]), and it solves the current goal
    immediately.  For example: *)

(** discriminate : ⊥ dans hypotheses => Resoud le but actuel *)

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.

(** We can proceed by case analysis on [n]. The first case is
    trivial. *)

  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

(** However, the second one doesn't look so simple: assuming [0
    =? (S n') = true], we must show [S n' = 0]!  The way forward is to
    observe that the assumption itself is nonsensical: *)

  - (* n = S n' *)
    simpl.

(** If we use [discriminate] on this hypothesis, Coq confirms
    that the subgoal we are working on is impossible and removes it
    from further consideration. *)

    intros H. discriminate H.
Qed.

(** This is an instance of a logical principle known as the _principle
    of explosion_, which asserts that a contradictory hypothesis
    entails anything, even false things! *)

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are _not_ showing that the conclusion of the
    statement holds.  Rather, they are showing that, if the
    nonsensical situation described by the premise did somehow arise,
    then the nonsensical conclusion would follow.  We'll explore the
    principle of explosion of more detail in the next chapter. *)

(** **** Exercise: 1 star, standard (discriminate_ex3)  *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros. discriminate H. Qed.
(** [] *)

(** The injectivity of constructors allows us to reason that
    [forall (n m : nat), S n = S m -> n = m].  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find convenient in a few
    places below: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)

(** 默认情况下，大部分策略会作用于目标公式并保持上下文不变。然而，
    大部分策略还有对应的变体来对上下文中的语句执行类似的操作。

    例如，策略 [simpl in H] 会对上下文中名为 [H] 的前提执行化简。
 *)

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** 类似地，[apply L in H] 会针对上下文中的前提 [H] 匹配某些
    （形如 [X → Y] 中的）条件语句 [L]。然而，与一般的 [apply] 不同
    （它将匹配 [Y] 的目标改写为子目标 [X]），[apply L in H] 会针对
    [X] 匹配 [H]，如果成功，就将其替换为 [Y]。

    换言之，[apply L in H] 给了我们一种"正向推理"的方式：
    根据 [X → Y] 和一个匹配 [X] 的前提，它会产生一个匹配 [Y] 的前提。
    作为对比，[apply L] 是一种"反向推理"：它表示如果我们知道 [X → Y]
    并且试图证明 [Y]， 那么证明 [X] 就足够了。

    下面是前面证明的一种变体，它始终使用正向推理而非反向推理 *)

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** 正向推理从给定的东西开始（即前提、已证明的定理）， 根据它们迭代地
    刻画结论直到抵达目标。反向推理从目标开始， 迭代地推理蕴含目标的东西，
    直到抵达前提或已证明的定理。

    如果你之前见过非形式化的证明（例如在数学或计算机科学课上）， 它们使用的
    应该是正向推理。通常，Coq 习惯上倾向于使用反向推理， 但在某些情况下，
    正向推理更易于思考。*)

(** **** Exercise: 3 stars, standard, recommended (plus_n_n_injective)  

    Practice using "in" variants in this proof.  (Hint: use
    [plus_n_Sm].) *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* Use [plus_n_Sm] Lemma *)
  - intros m H. simpl in H. destruct m as [| m'].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros m H. simpl in H. destruct m as [| m'].
    + discriminate H.
    + simpl in H. rewrite <- !plus_n_Sm in H. (* rewrite modifiers *)
      inversion H. apply IHn' in H1. rewrite H1. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)

(** 在 Coq 中进行归纳证明时，有时控制归纳假设的确切形式是十分重要的。 特别是在
    调用 [induction] 策略前，我们用 [intros] 将假设从目标移到上下文中时要十分小心。
    例如，假设我们要证明 [double] 函数式单射 — 即它将不同的参数映射到不同的结果：

       Theorem double_injective: forall n m,
         double n = double m -> n = m.

    其证明的开始方式有点微妙：如果我们以

       intros n. induction n.

    开始，那么一切都好。然而假如以

       intros n m. induction n.

    开始，就会卡在归纳情况中...*)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.

(** 此时，归纳假设 [IHn'] 不会给出 [n' = m'] — 会有个额外的 [S] 阻碍
    因此该目标无法证明。*)

      Abort.

(** What went wrong? *)

(** 问题在于，我们在调用归纳假设的地方已经将 [m] 引入了上下文中
    直观上，我们已经告诉了 Coq "我们来考虑具体的 [n] 和 [m]..."，
    而现在必须为这些具体的 n 和 m 证明 [double n = double m]，
    然后才有 [n = m]。

    下一个策略 [induction n] 告诉 Coq：我们要对 [n] 归纳来证明该目标。
    也就是说，我们要证明对于所有的 [n]，命题

      - [P n] = "if [double n = double m], then [n = m]"

    成立，需通过证明

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") and

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    如果我们仔细观察第二个语句，就会发现它说了奇怪的事情：
    即，对于一个具体的 [m]，如果我们知道

      - "if [double n = double m] then [n = m]"

    那么我们就能证明

       - "if [double (S n) = double m] then [S n = m]".

    要理解为什么它很奇怪，我们来考虑一个具体的 [m] — 比如说5。
    该语句就会这样说：如果我们知道

      - [Q] = "if [double n = 10] then [n = 5]"

    那么我们就能证明

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    但是知道 [Q] 对于证明 [R] 来说并没有任何帮助！（如果我们试着根据 [Q] 证明
    [R] from [Q]，就会以"假设 double (S n) = 10.."这样的句子开始， 不过之后
    我们就会卡住：知道 [double (S n)] 为 10 并不能告诉我们 [double n] 是否为 10，
    因此 [Q] 是没有用的。）*)

(** 当 [m] 已经在上下文中时，试图对 [n] 进行归纳来进行此证明是行不通的， 因为我们之后要尝试证明涉及每一个 n 的命题，而不只是单个 m。 *)

(** 对 [double_injective] 的成功证明将 [m] 留在了目标语句中 [induction] 
    作用于 [n] 的地方： *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.

(** 注意，此时的证明目标和归纳假设是不同的：证明目标要求我们证明更一般的事情
    （即为每一个 [m] 证明该语句），而归纳假设 [IH] 相应地更加灵活， 允许我们
    在应用归纳假设时选择任何想要的 [m]。*)

    intros m eq.

(** 现在我们选择了一个具体的 [m] 并引入了假设 [double n = double m]。 由于
    我们对 [n] 做了情况分析，因此还要对 [m] 做情况分析来保持两边"同步"。*)

    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.

(** 0 的情况很显然：*)

      discriminate eq.

    + (* m = S m' *)
      apply f_equal.

(** 到这里，由于我们在 [destruct m] 的第二个分支中，因此上下文中涉及
    到的 [m'] 就是我们开始讨论的 [m] 的前趋。由于我们也在归纳的 [S] 分支中，
    这就很完美了： 如果我们在归纳假设中用当前的 [m']（此实例由下一步的 [apply]
    自动产生） 实例化一般的 [m]，那么 [IHn'] 就刚好能给出我们需要的来结束此证明。*)

      apply IHn'. injection eq as goal. apply goal. Qed.

(** What you should take away from all this is that we need to be
    careful, when using induction, that we are not trying to prove
    something too specific: To prove a property of [n] and [m] by
    induction on [n], it is sometimes important to leave [m]
    generic. *)

(** The following exercise requires the same pattern. *)

(** **** Exercise: 2 stars, standard (eqb_true)  *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IH].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - intros m H. destruct m as [| m'].
    + discriminate.
    + simpl in H. apply IH in H.
      rewrite H. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (eqb_true_informal)  

    Give a careful informal proof of [eqb_true], being as explicit
    as possible about quantifiers. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** 在 [induction] 之前做一些 [intros] 来获得更一般归纳假设并不总是奏效。
    有时需要对量化的变量做一下重排。例如，假设我们想要通过对 [m] 而非 [n]
    进行归纳来证明 [double_injective]。*)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** 问题在于，要对 [m] 进行归纳，我们首先必须对 [n] 归纳。
    （如果我们不引入任何东西就执行 [induction m]，Coq 
    就会自动为我们引入 [n]）*)

(** 我们可以对它做什么？一种可能就是改写该引理的陈述使得 [m] 在 [n] 之前量化。
    这样是可行的，不过它不够好：我们不想调整该引理的陈述来适应具体的证明策略！
    我们更想以最清晰自然的方式陈述它。*)

(** 我们可以先引入所有量化的变量，然后重新一般化（re-generalize） 其中的一个
    或几个，选择性地从上下文中挑出几个变量并将它们放回证明目标的开始处。 
    用 generalize dependent 策略就能做到。*)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(** 我们来看一下此定理的非形式化证明。注意我们保持 [n] 的量化状态并通过归纳证明的命题，
    对应于我们形式化证明中依赖的一般化。

    _定理_：对于任何自然数 n 和 m，若 double n = double m，则 n = m。
    _Theorem_: For any nats [n] and [m], if [double n = double m], then
      [n = m].

    _Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
      any [n], if [double n = double m] then [n = m].

      - First, suppose [m = 0], and suppose [n] is a number such
        that [double n = double m].  We must show that [n = 0].

        Since [m = 0], by the definition of [double] we have [double n =
        0].  There are two cases to consider for [n].  If [n = 0] we are
        done, since [m = 0 = n], as required.  Otherwise, if [n = S n']
        for some [n'], we derive a contradiction: by the definition of
        [double], we can calculate [double n = S (S (double n'))], but
        this contradicts the assumption that [double n = 0].

      - Second, suppose [m = S m'] and that [n] is again a number such
        that [double n = double m].  We must show that [n = S m'], with
        the induction hypothesis that for every number [s], if [double s =
        double m'] then [s = m'].

        By the fact that [m = S m'] and the definition of [double], we
        have [double n = S (S (double m'))].  There are two cases to
        consider for [n].

        If [n = 0], then by definition [double n = 0], a contradiction.

        Thus, we may assume that [n = S n'] for some [n'], and again by
        the definition of [double] we have [S (S (double n')) =
        S (S (double m'))], which implies by injectivity that [double n' =
        double m'].  Instantiating the induction hypothesis with [n'] thus
        allows us to conclude that [n' = m'], and it follows immediately
        that [S n' = S m'].  Since [S n' = n] and [S m' = m], this is just
        what we wanted to show. [] *)

(** Before we close this section and move on to some exercises,
    let's digress briefly and use [eqb_true] to prove a similar
    property of identifiers that we'll need in later chapters: *)

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, recommended (gen_dep_practice)  

    Prove this by induction on [l]. *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a name that
    has been introduced by a [Definition] so that we can manipulate
    its right-hand side.  For example, if we define... *)

Definition square n := n * n.

(** ... and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ... we appear to be stuck: [simpl] doesn't simplify anything at
    this point, and since we haven't proved any other facts about
    [square], there is nothing we can [apply] or [rewrite] with.

    To make progress, we can manually [unfold] the definition of
    [square]: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these it is not hard
    to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** At this point, some discussion of unfolding and simplification is
    in order.

    You may already have observed that tactics like [simpl],
    [reflexivity], and [apply] will often unfold the definitions of
    functions automatically when this allows them to make progress.
    For example, if we define [foo m] to be the constant [5]... *)

Definition foo (x: nat) := 5.

(** .... then the [simpl] in the following proof (or the
    [reflexivity], if we omit the [simpl]) will unfold [foo m] to
    [(fun x => 5) m] and then further simplify this expression to just
    [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** However, this automatic unfolding is somewhat conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the [match] are identical, so it gives up on
    unfolding [bar m] and leaves it alone.  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that cannot itself be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone. *)

(** At this point, there are two ways to make progress.  One is to use
    [destruct m] to break the proof into two cases, each focusing on a
    more concrete choice of [m] ([O] vs [S _]).  In each case, the
    [match] inside of [bar] can now make progress, and the proof is
    easy to complete. *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress. *)

(** A more straightforward way to make progress is to explicitly tell
    Coq to unfold [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [destruct] to finish the
    proof without thinking too hard. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where [destruct] is used to
    perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (n =? 3) then ... else ...].  But either
    [n] is equal to [3] or it isn't, so we can use [destruct (eqb
    n 3)] to let us reason about the two cases.

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)

(** **** Exercise: 3 stars, standard, optional (combine_split)  

    Here is an implementation of the [split] function mentioned in
    chapter [Poly]: *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(** Prove that [split] and [combine] are inverses in the following
    sense: *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The [eqn:] part of the [destruct] tactic is optional: We've chosen
    to include it most of the time, just for the sake of
    documentation, but many Coq proofs omit it.

    When [destruct]ing compound expressions, however, the information
    recorded by the [eqn:] can actually be critical: if we leave it
    out, then [destruct] can sometimes erase information we need to
    complete a proof. 

    For example, suppose we define a function [sillyfun1] like
    this: *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

(** Now suppose that we want to convince Coq of the (rather
    obvious) fact that [sillyfun1 n] yields [true] only when [n] is
    odd.  If we start the proof like this (with no [eqn:] on the
    destruct)... *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

(** ... then we are stuck at this point because the context does
    not contain enough information to prove the goal!  The problem is
    that the substitution performed by [destruct] is quite brutal --
    in this case, it thows away every occurrence of [n =? 3], but we
    need to keep some memory of this expression and how it was
    destructed, because we need to be able to reason that, since [n =?
    3 = true] in this branch of the case analysis, it must be that [n
    = 3], from which it follows that [n] is odd.

    What we want here is to substitute away all existing occurences of
    [n =? 3], but at the same time add an equation to the context that
    records which case we are in.  This is precisely what the [eqn:]
    qualifier does. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        [eqn:] again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.  Qed.

(** **** Exercise: 2 stars, standard (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Review *)

(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [injection]: reason by injectivity on equalities
        between values of inductively defined types

      - [discriminate]: reason by disjointness of constructors on
        equalities between values of inductively defined types

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (eqb_sym)  *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (eqb_sym_informal)  

    Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [(n =? m) = (m =? n)].

   Proof: *)
   (* FILL IN HERE 

    [] *)

(** **** Exercise: 3 stars, standard, optional (eqb_trans)  *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (split_combine)  

    We proved, in an exercise above, that for all lists of pairs,
    [combine] is the inverse of [split].  How would you formalize the
    statement that [split] is the inverse of [combine]?  When is this
    property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split (combine l1 l2) = (l1,l2)] to be true?) *)

Definition split_combine_statement : Prop
  (* ("[: Prop]" means that we are giving a name to a
     logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise)  

    This one is a bit challenging.  Pay attention to the form of your
    induction hypothesis. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge)  

    Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (eqb 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (eqb 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_4 : existsb evenb [] = false.
Proof. (* FILL IN HERE *) Admitted.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)



(* Wed Jan 9 12:02:44 EST 2019 *)
