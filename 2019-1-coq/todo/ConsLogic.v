(** * Constructive Logic: Coq 中的构造主义逻辑系统 *)

Set Warnings "-notation-overridden,-parsing".
(** From LF Require Export Basics. *)

(* ################################################################# *)
(** * Coq vs. 集合论 *)

(** Coq 的逻辑核心，即_'归纳构造演算（Calculus of Inductive Constructions）'_系统，
    在很多重要的方面不同于数学家用来写下精确而严谨的证明的形式化系统。
    例如，在主流的纸笔数学家中使用最普遍的_'策梅洛-弗兰克尔集合论（ZFC）'_中，
    一个数学对象可同时属于不同的集合；而在 Coq 的逻辑中，一个项最多只属于一个类型。
    这些不同之处需要人们用稍微不同的方式来描述非形式化的数学概念，但总的来说，
    它们都是非常自然而易于使用的。例如，在 Coq 中我们一般不说某个自然数 [n]
    属于偶数集合，而是说 [even n] 成立，其中的 [even : nat -> Prop] 描述了偶数的性质。

    然而在某些情况下，将标准的数学论证翻译到 Coq 中会十分繁琐甚至是不可能的，
    除非我们引入新的公理来丰富其逻辑核心。作为本章的结尾，
    我们将探讨这两个世界之间最显著的区别。 *)

(* ================================================================= *)
(** ** 函数的外延性 *)

(** 目前为止我们所看见的相等关系断言基本上都只考虑了归纳类型的元素
    （如 [nat]、[bool] 等等）。然而由于 Coq 的相等关系运算符是多态的，
    因此它们并不是唯一的可能。特别是，我们可以写出宣称_'两个函数相等'_的命题： *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** 在一般的数学研究中，对于任意的两个函数 [f] 和 [g]，只要它们产生的结果相等，
    那么它们就被认为相等：

    (forall x, f x = g x) -> f = g

    这被称作_'函数的外延性原理'_。 *)

(** 不甚严谨地说，所谓“外延性”是指某个对象可观察到的行为。
    因此，函数的外延性就是指函数的标识完全由其行为来决定。
    用 Coq 的术语来说，就是函数的身份视其被应用后的结果而定。 *)

(** 函数的外延性并不在 Coq 的基本公理之内，因此某些“合理”的命题是不可证明的： *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* 卡住了 *)
Abort.

(** 然而，我们可以用 [Axiom] 指令将函数的外延性添加到 Coq 的核心逻辑系统中。 *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** 使用 [Axiom] 的效果与陈述一个定理并用 [Admitted] 跳过其证明相同，
    不过它会提醒读者这是一个公理，我们无需证明！*)

(** 现在我们可以在证明中调用函数的外延性了： *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** 当然，在为 Coq 添加公理时必须十分小心，因为这有可能会导致系统
    _'不一致'_，而当系统不一致的，任何命题都能在其中证明，包括 [False]
    和 [2+2=5]！

    不幸的是，并没有一种简单的方式能够判断添加某条公理是否安全：
    一般来说，确认任何一组公理的一致性都需要训练有素的专家付出艰辛的努力。

    然而，我们已经知道了添加函数外延性后的公理系统_'确实是'_一致的。 *)

(** 我们可以用 [Print Assumptions] 指令查看某个证明依赖的所有附加公理。 *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** 练习：4 星, standard (tr_rev_correct)  

    列表反转函数 [rev] 的定义有一个问题，它会在每一步都执行一次 [app]
    调用，而运行 [app] 所需时间与列表的大小线性渐近，也就是说 [rev]
    的时间复杂度与列表长度成平方关系。我们可以用以下定义来改进它： *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** 此版本是_'尾递归的'_，因为对函数自身的递归调用是需要执行的最后一步操作
    （即，在递归调用之后我们并不执行  [++] ）。
    一个足够好的编译器会对此生成十分高效的代码。请证明以下两个定义等价。 *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* 请在此处解答 *) Admitted.
(** [] *)
(* ================================================================= *)
(** ** 经典逻辑 vs. 构造逻辑 *)

(** 我们已经知道了，在定义 Coq 函数时是无法判断命题 [P] 是否成立。
    然而_'证明'_也存在类似的限制！换句话说，以下推理原则即便符合直觉，
    不过在 Coq 中它是不可证明的： *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** 为了在操作上理解为何如此, 回忆一下，在证明形如 [P \/ Q]
    的陈述时，我们使用了 [left] 与 [right] 策略，它们能够有效地知道析取的哪边成立。
    然而在 [excluded_middle] 中，[P] 是被全称量化的_'任意'_命题，我们对它一无所知。
    我们没有足够的信息来选择使用 [left] 或 [right] 中的哪一个。就像 Coq
    因为缺乏信息而无法在函数内部机械地确定 [P] 是否成立一样。 *)

(** 然而，如果我们恰好知道 [P] 与某个布尔项互映，那么就能很轻易地知道它是否成立了：
    我们只需检查 [b] 的值即可。 *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** 特别来说，对于自然数 [n] 和 [m] 的 [n = m] 而言，排中律是成立的。 *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** 通用的排中律默认在 Coq 中并不可用，这一点或许很奇怪，毕竟，
    任何给定的断言都是非真即假的。尽管如此，不假设排中律的成立仍有其有限：
    Coq 中的陈述可以构造出比标准数学中同样陈述更强的断言。特别是，
    如果存在 [exists x, P x] 的 Coq 证明，那么我们就能直接给出一个使 [P x]
    得证的值 [x]。换言之，任何关于存在性的证明必定是_'构造性'_的。 *)

(** 像 Coq 一样不假设排中律成立的逻辑系统被称作_'构造逻辑'_。

    像 ZFC 这样更加传统的，排中律对于任何命题都成立的逻辑系统则被称作_'经典逻辑'_。 *)

(** 以下示例展示了为何假设排中律成立会导致非构造性证明：

    _'命题'_：存在无理数 [a] 和 [b] 使得 [a ^ b] 为有理数。

    _'证明'_：易知 [sqrt 2] 为无理数。若 [sqrt 2 ^ sqrt 2] 为有理数，
    那么可以取 [a = b = sqrt 2] 证明结束；否则 [sqrt 2 ^ sqrt 2] 为无理数。
    此时，我们可以取 [a = sqrt 2 ^ sqrt 2] 和 [b = sqrt 2]，因为
    [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2].  []

    看到发生什么了吗？我们使用排中律在不知道 [sqrt 2 ^ sqrt 2]
    是否为有理数的情况下就分别考虑了这两种情况！因此，我们知道了这样的
    [a] 和 [b] 存在，但却无法确切知道它们的值（至少使用此论据来说如此）。

    即便构造逻辑很有用，它也有自身的限制：存在很多容易用经典逻辑证明的命题，
    用构造证明会更加复杂，而对于某些已知的命题而言这样的构造性证明甚至不存在！
    幸运的是，排中律和函数外延性一样都是与 Coq 的逻辑系统兼容的，
    我们可以安全地将它作为公理添加到 Coq 中。然而，在本书中我们不必如此：
    我们所涉及的结构都可以完全用构造逻辑得到，所需的额外代价则微不足道。

    我们需要一定的实践才能理解哪些证明技巧不应在构造推理中使用，
    而其中的反证法尤为臭名昭著，因为它会导向非构造性证明。这里有个典型的例子：
    假设我们想要证明存在 [x] 具有某种性质 [P]，即存在 [P x]。我们先假设结论为假，
    也就是说 [~ exists x, P x]。根据此前提，不难推出 [forall x, ~ P x]。
    如果我们能够根据此中间事实得到矛盾，就能得到一个存在性证明而完全不必指出一个
    [x] 的值使得 [P x] 成立！

    从构造性的角度来看，这里存在着技术上的瑕疵，即我们试图通过对
    [~ ~ (exists x, P x)] 的证明来证明 [exists x, P x]。从以下练习中我们会看到，
    允许自己从任意陈述中去掉双重否定等价于引入排中律。因此，只要我们不引入排中律，
    就无法在 Coq 中编码此推理。 *)

(** **** 练习：3 星, standard (excluded_middle_irrefutable)  

    证明通用排中律公理与 Coq 的一致性需要复杂的推理，而且并不能在 Coq
    自身中进行。然而，以下定理蕴含了假设可判定性公理（即排中律的一个特例）
    成立对于任何_'具体的'_命题 [P] 而言总是安全的。之所以如此，
    是因为我们无法证明这类公理的否定命题。假如我们可以的话，就会同时有
    [~ (P \/ ~P)] 和 [~ ~ (P \/ ~P)]（因为根据以下练习， [P] 蕴含 [~ ~ P]），
    而这会产生矛盾。但因为我们不能，所以将 [P \/ ~P] 作为公理加入是安全的。 *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (not_exists_dist)  

    在经典逻辑中有这样一条定理，它断言以下两条命题是等价的：

    ~ (exists x, ~ P x)
    forall x, P x

    之前的 [dist_not_exists] 证明了此等价式的一个方向。有趣的是，
    我们无法用构造逻辑证明另一个方向。你的任务就是证明排中律蕴含此方向的证明。 *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, standard, optional (classical_axioms)  

    对于喜欢挑战的读者，以下练习来自于 Bertot 与 Casteran 所著的
    Coq'Art 一书中第 123 页。以下四条陈述的每一条，加上 [excluded_middle]
    可以认为刻画了经典逻辑。我们无法在 Coq 中证明其中的任意一条，
    不过如果我们希望在经典逻辑下工作的话，可以安全地将其中任意一条作为公理添加到
    Coq 中而不会造成不一致性。

    请证明所有五个命题都是等价的（这四个再加上 [excluded_middle]）。*)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* 请在此处解答 

    [] *)

(* Fri Jul 19 00:32:20 UTC 2019 *)
