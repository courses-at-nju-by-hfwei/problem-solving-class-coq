(** * Logic: Coq 中的逻辑系统 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Basics.

(**
  "逻辑是不可战胜的，因为反对逻辑还得使用逻辑。" By 谁说的来着?
  
  本节介绍一阶谓词逻辑 
  (说它是一阶谓词逻辑并不严格，我们在本节的最后部分讨论) 
  的 _'自然推理系统' (Natural Deduction System)_。
  系统，封闭之结构也;
  推理，证明之路径也;
  自然，“无他，但手熟尔”。
  这个推理系统，我们基本每天都在使用 (或者误用)。
  本节只不过是告诉你如何在 Coq 中使用这个推理系统证明定理 
  (有 Coq 盯着你，你就再也不会误用它们了)。
  
  在一阶谓词逻辑中，我们会考虑各种 _'命题' (Proposition)_，包括
  _'合取' (Conjunctive?)_ 命题、_'析取' (Disjunctive)_ 命题、
  _'否定' (Negative)_ 命题、_'蕴含 (Implication)'_ 命题、
  _'等价' (Equivalence)_ 命题、_'相等性' (Equality)_ 命题、
  _'存在' (Existence)_ 命题 以及 _'全称' (Forall)_ 命题。 
  
  关于逻辑，首先需要介绍的一个概念就是 _'命题' (Proposition)_。
  什么是命题? 命题就是可以判断真假的语句。
  什么是语句? 语句是不含自由变量的公式。
  什么是真? 什么是假? 这个问题就深了。我不敢妄言。
  在这里，我们采用直觉的定义方式，不深究真与假的概念。
  所谓命题，就是可以判断真假的不含自由变量的公式。
  (又有学生问: 什么是变量? 什么是自由变量? 什么是公式?)
  我们之前证明过的 [Example]、[Lemma]、[Theorem] 都是命题。
  如果这个定义还是让你疑惑重重，你不妨采取下面这种定义方式:
  "我不知道什么是命题，但是当我见到它的时候，我就知道了"
  ("I Know It When I See It")
*)

(**
  在 Coq 中，作为一个表达式，命题也是有类型的。
  它的类型是 [Prop]，即 _'命题类型'_。
*)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

Check 2 = 2.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

(** 
  _'是'_一个命题与该命题_'为真'_ (或者说，_'可被证明' (Provable)_) 是两回事。
  后者是计算机科学与数理逻辑的重要研究对象。 
*)

(**
  在 Coq 中，命题是 _'一等对象（First-Class Object）'_，
  我们可以像操作其它实体那样操作命题，比如:
  - (1) 为命题命名，并在之后引用它的名字。
  - (2) 命题可以作为函数的返回值。 
*)

(** (1) 我们可以用 [Definition] 为命题命名，并在之后引用它的名字。*)

Definition plus_fact : Prop := (* ": Prop" 显式地指明了类型，可以省略。*) 
  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

(** 
  (2) 命题可以作为函数的返回值。这类函数接受某些类型的参数，返回一个命题。
  实际上，这类函数定义了其参数的某种_'性质' (Property)_。 
*)

(** 
  例如，函数 [is_three] 接受自然数 [n]，返回一个命题断言该数字等于 3。
  它定义了自然数的"是否等于3"的性质 (是的，这个性质很无聊)。
*)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

Theorem three_is_three :
  is_three(3).
Proof. unfold is_three. reflexivity. Qed.

(** 我们还没有介绍过 [unfold] 证明策略。但是聪明的你应该能猜出它的含义与用法。*)

(** 
  函数 [injective] 定义了一个函数是否是 _'单射函数' (Injective Functions)_。
  定义中的 "[{A B}]" 表示 [A]、[B] 是两个参数化类型，
  我们会在后续介绍，这里可以当作它们不存在。
*)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

(** 
  相等关系运算符 [=] 也是一个返回 [Prop] 的函数。
  表达式 [n = m] 只是 [eq n m] 的 _'语法糖' (Syntax Sugar?)_。
*)
Check @eq. (* 暂时忽略 "[@]" 的含义与用法。*)
(* ===> forall A : Type, A -> A -> Prop *)

(** 
  你可以使用 [Print eq] 提前偷窥一下 [eq] 的定义。
  怎么样? 看不懂吧。稍安勿躁。
*)
Print eq.
(* ################################################################ *)
(** * 逻辑联结词 *)

(**
  TODO: 作为引子，介绍一下自然推理系统的对称性特点。
*)
(* ================================================================ *)
(** ** 合取 *)

(** 
  命题 [A /\ B] 表示命题 [A] 与 [B] 的_'合取'_（即_'逻辑与'_）
  [A /\ B] 为真当且仅当 [A] 与 [B] 均为真。
  [A /\ B] 是 [and A B] 的语法糖。
*)

Check and.
(* ===> and : Prop -> Prop -> Prop *)
Print and. (* 偷窥一下 [and] 的定义 *)

(** 
  要证明 [A /\ B]，只需分别证明 [A] 与 [B]。
  在 Coq 中，[split] 策略会为目标 [A /\ B] 生成两个子目标 [A] 与 [B]。 
*)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(**
  对于任意命题 [A] 和 [B]，如果 [A] 为真且 [B] 为真，则 [A /\ B] 也为真。
  这个推理规则被称为 "/\-intro"。
  "intro" 表示在推导过程中 _引入_ 了 "and"。
*)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

(**
  在上面的证明中，我们使用了一种新的证明策略 [apply]。
  当证明目标 G 与上下文中的某个前提 H 完全相同时，
  我们就可以使用 [apply H] 完成证明 
  (也可以使用 [exact H] 或者 [assumption])。
  关于 [apply] 的其余用法，我们在后续介绍。
*)

(** **** 练习：2 星, standard (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(**
  如果当前 _证明上下文_ 中存在形如 [A /\ B] 的前提 [H]，
  我们可以使用 [destruct H as [HA HB]] 将 [H] 转化为 [HA] 和 [HB]
  两个新的前提。这样，我们就可以单独使用 [A] 与 [B] 进行证明了。
*)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 你是否还记得 "intro pattern"? *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm]. (* "intro pattern " *)
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** **** 练习：2 星, standard (and_example3) *)
(**
  证明如下定理。你可以需要使用 [and_exercise] 定理与 [assert] 策略 
  (又忘了吧? 不要沮丧。学习就是不断重复、不断升华的过程。)。 
*)
Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** 
  显然，[A /\ B] 蕴含 [A]，也蕴含 [B]。
  接下来两个引理 ([and_elim_left] 与 [and_elim_right])
  构成 "/\-elimination" 规则。
*)

Lemma and_elim_left : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

(** **** 练习：1 星, standard, optional (proj2)  *)
Lemma and_elim_right : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** [and] 满足交换律。*)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - (* Q *) apply HQ.
  - (* P *) apply HP.
Qed.

(** **** 练习：2 星, standard (and_assoc) *)
(**
  [and]满足结合律。请完成定理 [and_assoc] 的证明。
  请注意学习 [intros [HP [HQ HR]]] 的用法。
*)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* ================================================================= *)
(** ** 析取 *)

(** 
  命题 [A \/ B] 表示 [A] 与 [B] 的 _'析取' (即 "逻辑或")_。
  [A \/ B] 为真当且仅当 [A] 与 [B] 中至少有一个为真。
  [A \/ B] 是 [or A B] 的语法糖。
*)
Check or. (* 你应该能猜得到。*)
Print or. 
(* 偷窥一下 [or] 的定义。你猜到了吗? 注意 [or_introl] 与 [or_intror]。*)

(** 
  要证明 [A \/ B] 成立，只需要证明 [A] 成立或者 [B] 成立。
  这就是 [\/-intro-left] 与 [\/-intro-right] 规则。
  在 Coq 中，我们可以分别使用 [left] 与 [right] 策略选择要证明的子目标。
*)

Lemma or_intro_left : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** **** 练习：1 星, standard (or_intro_right)  *)
(* 请给出引理 [or_intro_right] 并证明。*)
  (* 请在此处解答 *)
(** [] *)

(** 引理 [zero_or_succ] 需要同时使用 [left] 和 [right]。*)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [ | n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** 练习：1 星, standard (mult_eq_0) *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. 
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** 
  如果已知 [P \/ Q]，我们想证明目标 [R]。
  我们只需证明 [P => R] 以及 [Q => R]。
  这就是 "\/-elimination" 规则，类似于分情形讨论。
  是的，在 Coq 中，我们可以使用 [destruct] 或者 [intros pattern]
  将"已知 [P\/ Q]，证明目标 [G]" 转变成两个任务:
  - 已知 [P]，证明 [G]
  - 已知 [Q]，证明 [G]。
*)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* [Hn | Hm] 隐式地对 [n = 0 \/ m = 0] 进行分情形讨论 *)
  intros n m [Hn | Hm].
  - (* 情形 [n = 0] *)
    rewrite Hn. reflexivity.
  - (* 情形 [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** **** 练习：1 星, standard (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* ================================================================= *)
(** ** 假命题与否定 
  很多时候，我们需要证明某个命题 [A] 不成立，
  即证明 [~A] 成立。
  [~A] 是 [not A] 的语法糖。
*)
Check not. (* 恭喜你，猜对了。*)
(* ===> not : Prop -> Prop *)
Print not. (* 你猜到了吗? *)
(**
  ===> not = fun A : Prop => A -> False
  
  我们来解释一下这个定义。
  - 首先，[not] 是一个函数 [fun A : Prop => A -> False]。
  - [fun A : Prop => A -> False] 是匿名函数 (没有函数名)，
    接受一个命题 [A : Prop]，返回 (=>) 一个命题 [A -> False]。
  因此，[~A] 就是 [A -> False]。
  换句话说，Coq 使用 [A] 能蕴含 False，来表示 [A] 不成立。
  
  那么，[False] 是什么呢?
  [False] 是 Coq 标准库中定义的矛盾性命题。
*)

Check False. (* [False] 也是个命题。*)
(* ===> False : Prop *)
Print False. (* 咦? 出 Bug 了吗? *)
(**
  ===> Inductive False : Prop :=
  
  [False] 的定义为空。
  这意味着，你无法在 Coq 中证明它。
*)

(**
  定理 [ex_falso_quodlibet] (拉丁文) 描述了 [False-elimination] 规则，
  它的含义是 "从谬误出发，你能够证明任何命题。"
  (王小波关于"荒诞的年代"的那句话是怎么说的来着?)
  
  如果 [H : False] 作为前提出现在上下文中，
  那么我们就可以使用 [destruct H] 来完成任何待证目标。 
*)

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(** 
  [ex falso quodlibet] (缩写 EFQ) 也称为 _"Principle of Explosion"_。
  形象地讲，[False] 是枚炸弹，[destruct False] 就是在拆炸弹。
  然后，Bang ……
  
  因此，一旦我们设法向上下文中引入了 [False]，我们也就完成了证明。
*)

(* 再看一个简单的例子 [not_False]。*)
Theorem not_False :
  ~ False.
Proof.
  unfold not. (* 我们经常需要展开 [not] 的定义。*)
  intros H. (* 展开 [not] 之后，通常都会跟着一个 [intros]。*)
  destruct H. (* 当然，这里也可以使用 [apply H]。*)
Qed.

(* [double_neg] 定理涉及 "双重否定"。*)
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not. intros G. (* [unfold not] + [intros] *)
  apply G. (* 注意观察待证目标的变化。下面解释该行。*)
  apply H.
Qed.

(**
  定理 [double_neg] 的证明使用了 [apply] 策略的另一种用法。
  
  之前，当待证明的目标 [Goal] 与上下文中的某个前提 [A] 完全一样时，
  我们使用 [apply A] 即可完成证明。
  
  在上面的证明中，[G] 是一个蕴含式 [G : P -> False]，
  当前待证目标 [Goal] 是 [Goal : False]。
  注意到待证目标与蕴含式 [G] 中的结论相同 
  (更宽泛地讲，只需要它们可以匹配)，
  此时，[apply G] 将 [G] 作用到当前待证目标上，
  其效果相当于 _逆向 (Backward)_ 使用蕴含式 [G]:
  它将待证目标 [False] 转化为 [P]。
  背后的推理是: 要证明 [False] 成立，根据前提 [G : P -> False]，
  只需证明 [P] 成立。
  这实际上是 [->-elimination] 规则，也就是 _'modus ponens'_ 规则。
*)

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. (* 对 [HP] _正向 (Forward)_ 应用蕴含式。*)
  destruct HP.
Qed.

(**
  上面的证明使用了 [apply] 策略的第三种用法:
  [HNP] 是蕴含式 [HNP : P -> False]。
  [HP] 是 [HP : P]。
  注意到 [HP] 与 [HNP] 的前件相同，
  此时，[apply HNP in HP] 是在正向应用 _'modus ponens'_ 规则:
  已知 [P -> False] 与 [P]，推导出 [False]。
  
  注意: [apply I in H] 会改变 [H]。
  如果不想改变 [H]，可以使用 [apply I in H as ...] 变体。
*)

(** **** 练习：2 星, standard, optional (not_implies_our_not) *)  
(**
  了解了 [apply] 的用法，现在你可以证明定理 
  [not_implies_our_not] 了。
  它实际上指出了 [not] 的另一种定义方法:
  我们可以使用 "[P] 可以蕴含一切命题 ([Q])" 定义 [not P]。  
*)

Fact not_implies_forall_implication : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

Fact forall_implication_implies_not : forall (P : Prop),
  (forall (Q : Prop), P -> Q) -> (~ P).
Proof.
  intros P PQ.
  unfold not. intro HP.
  apply (PQ False). (* 你还记得我们为什么可以这样使用 [PQ False] 吗? *)
  apply HP.
Qed.

(** **** 练习：2 星, standard, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：1 星, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(**  
  我们用 [x <> y] 表示 (~ (x = y))。
  Notation "x <> y" := (~(x = y)).
*)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* 注意: [] 对 [b] 作了分情形讨论。*)
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet. (* 观察待证目标的变化。想想为什么? *)
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Coq 为 [ex_falso_quodlibet] 提供了内建的策略 [exfalso]。*)
Print exfalso.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.  (* <=== *)
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.
(* ================================================================= *)
(** ** 真值 *)

(**
  [True] 也是 Coq 预定义的命题，它代表真。
  我们已经知道 [False] 的定义为空，那么 [True] 的定义是什么呢?
*)
Check True.
(* ===> True : Prop *)
Print True.
(**
  ===> [Inductive True : Prop := I : True]
  
  [True] 只有一种构造方式，那就是 [I]。
  因此，要证明 [True]，我们只需要 [apply I] 即可。
*)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** 
  [True] 作为前提不携带任何有用的信息，
  因此没有必要引入 [True-elimination] 规则。
*)
(* ================================================================= *)
(** ** 逻辑等价 *)

(** 
  命题 [A <-> B] 表示 [A] 成立当且仅当 [B] 成立。
  [A <-> B] 是 [iff A B] 的语法糖。
*)
Check iff.
(* ===> iff : Prop -> Prop -> Prop *)
Print iff.
(**
  ===> iff = fun A B : Prop => (A -> B) /\ (B -> A)
  
  我们详细讲解过 [not] 的定义。
  现在，你应该能独立理解 [iff] 的定义了。
*)

(**
  在 Coq 中，[A <-> B] 即为 [A -> B] 与 [B -> A] 的合取。
  - 当 [A <-> B] 作为前提 [H] 出现在上下文中时，
    我们可以使用 [destruct H as [HAB HBA]] 
    将它拆成两个前提 [HAB : A -> B] 与 [HBA : B -> A]。
  - 当 [A <-> B] 作为目标时，
    我们可以使用 [split] 将它拆成两个子目标
    [A -> B] 与 [B -> A]。
    
  依照上述证明方法，我们可以证明 [iff] 具有对称性 (定理 [iff_sym])。
*)
Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

(** **** 练习：1 星, standard, optional (iff_properties) *)
(**
  请证明 [iff] 具有自反性 (定理 [iff_refl]) 与传递性 (iff_trans)。
  (你可能还不知道什么是自反性，什么是对称性，什么是传递性。不要紧。
  我们会在后续课程介绍。)
*)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：3 星, standard (or_distributes_over_and)  *)
(** 请证明如下分配律。*)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** 
  我们之前介绍过的 [rewrite] 和 [reflexivity] 
  不仅可以用于相等关系，还可用于 [iff] 命题。
  为了开启此行为，我们需要导入库 Setoids.Setoid。
*)
From Coq Require Import Setoids.Setoid.

(**
  为了演示 [rewrite]、[reflexivity] 在 [iff] 上的作用，
  我们先做一些准备工作。
*)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0. (* 我怎么能记得住这么琐碎的定理! *)
  - apply or_example. (* 天呐，连 [Example] 都要记住吗?! *)
Qed. (* 不需要记住。我们的大脑有更重要的事情要处理。这里只是为了演示。*)

(**
  我们将定理 [or_assoc] 的证明留作练习。
  一点提示: [intro [HP | [HQ | HR]]]。
*)
Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** 
  现在，我们利用 [mult_0] 与 [or_assoc] 证明 [mult_0_3]。
  注意，我们可以对 [iff] 命题使用 [rewrite] 与 [reflexivity]。
*)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

(** 
  此外，[apply] 策略也可以用在 [<->] 上。
  这时，Coq 会尝试应用正确的方向。
*)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.
(* ================================================================= *)
(** ** 存在量词 *)

(**
  命题 [exists x : T, P] 表示存在类型为 [T] 的 [x]，
  使得性质 [P] 对 [x] 成立 (或说，[x] 满足性质 [P])。
  [exists] 是 _'存在量词_。
  (如果 Coq 能从上下文中推断出 [x] 的类型，那么 [: T] 也可以省略。
  但并不建议初学者这么做。)
*)

(** 
  要证明形如 [exists x, P] 的命题，
  我们只需(而且"必须"; 下一节 "ConsLogic.v" 解释)
  证明 [P] 对于某个特定的 [x] 成立。
  我们称 [x] 为 [exists x, P] 的例证。 
  这对应于 (逆用) "exists-intro" 规则。
  
  在 Coq 中，上述证明分为两步:
  - 使用 [exists t] 策略告诉 Coq 我们认为 [t] 是满足要求的 [x]。
    此时，证明目标变成 [P x]。
  - 证明新目标 [P x]。
*)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. (* 注意待证目标的变化 *)
  reflexivity.
Qed.

(**
  如果形如 [H: exists x, P] 的命题作为前提出现在上下文中，
  我们可以使用 [destruct H as [x Px]] (或者 intros) 将它拆分成
  一个例证 [x] 与 [x] 满足性质 [P] 的前提 [Px : P x]。
  在之后的证明中，我们就可以使用 [x] 与前提 [Px] 了。
  这对应于 "exists-elimination" 规则。
  (新引入的前提 [Px] 在使用 "exists-elimination"规则时
  会被 discharged (这个词该怎么翻译???) 掉。)
*)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* 注意观察上下文的变化 *)
  exists (2 + m).
  apply Hm.
Qed.

(** **** 练习：1 星, standard, recommended (dist_not_exists) *) 
(**
  请证明定理 [dist_not_exists]:
  "[P] 对所有 [x] 成立" 蕴含 "不存在 [x] 使得 [P x] 不成立"。
  
  另外，请思考如何证明另一个方向的蕴含关系?
  在 "ConsLogic.v" 中，我们会给出答案。
*)

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：2 星, standard (dist_exists_or) *)  
(** 请证明定理 [dist_exists_or]: "存在"对"析取"满足分配律。*)

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* 请在此处解答 *) 
Admitted.
(** [] *)
(* ================================================================= *)
(** ** 全称量词 *)
(**
  命题 [forall x : T, P] 表示对于所有的类型为 [T] 的 [x]，
  性质[P] 都对 [x] 成立 (或者说，[x] 都满足性质 [P])。
  我们已经见识过很多涉及全称量词的命题与证明了。
  这里，我们从自然推理系统的角度重新审视之前使用的证明策略。
*)

(** **** 练习：3 星, standard (combine_odd_even)  
  函数 [combine_odd_even] 接受两个定义在自然数上的性质 
  (类型为 [nat -> Prop]) [Podd] 与 [Peven]，
  返回性质 (类型为 [nat -> Prop]) [P]，
  使得当 [n] 为奇数时 [P n] 等价于 [Podd n]，否则等价于 [Peven n]。
*)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  := (fun n => (if (oddb n) then Podd n else Peven n)).

(** 
  请证明以下三个关于 [combine_odd_even] 的定理。
  注意定理的命名 (intro, elimination)。
*)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* ================================================================= *)
(** ** 命题与布尔值 *)

(** 我们已经知道在 Coq 中有两种编码逻辑事实的方式了，即使用_'布尔值'_
    （类型为 [bool]）和_'命题'_（类型为 [Prop]）。

    例如，我们可以通过以下两种方式来断言 [n] 为偶数： *)

(** [evenb n] 求值为 [true]： *)
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

(** 或者存在某个 [k] 使得 [n = double k]： *)
Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

(** 当然，如果二者刻画的偶数性描述的不是同一个自然数集合，那么会非常奇怪！
    幸运的是，我们确实可以证明二者相同... *)

(** 首先我们需要两个辅助引理。 *)
Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** 练习：3 星, standard (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* 提示：使用 [Induction.v] 中的 [evenb_S] 引理。  *)
  (* 请在此处解答 *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** 此定理说明，逻辑命题 [exists k, n = double k] 的真伪对应布尔计算 [evenb n]
    的真值。 *)

(** 类似地，以下两种 [n] 与 [m] 相等的表述等价：
      - (1) [n =? m] 值为 [true]；
      - (2) [n = m]。
    同样，二者的记法也等价。 *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

(** 然而，即便布尔值和某个断言的命题式在逻辑上是等价的，但它们在_'操作上'_
    也可能不一样。 *)

(** 在前面的偶数例子中，证明 [even_bool_prop] 的反向部分（即
    [evenb_double]，从命题到布尔表达式的方向）时，我们对
    [k] 进行了简单的归纳。而反方向的证明（即练习 [evenb_double_conv]）
    则需要一种聪明的一般化方法，因为我们无法直接证明
    [(exists k, n = double k) -> evenb n = true]。 *)

(** 对于这些例子来说，命题式的声明比与之对应的布尔表达式要更为有用，
    但并非总是如此。例如，我们无法在函数的定义中测试一般的命题是否为真，
    因此以下代码片段会被拒绝： *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq 会抱怨 [n = 2] 的类型是 [Prop]，而它想要一个 [bool]
    类型的元素（或其它带有两个元素的归纳类型）。此错误信息的原因与 Coq
    核心语言的_'计算性'_特质有关，即它能表达的所有函数都是可计算且完全的。
    这样设计的的原因之一是为了能从 Coq 开发的代码中提取出可执行程序。
    因此，在 Coq 中 [Prop] _'并没有'_一种通用的情况分析操作来确定
    任意给定的命题是否为真，一旦存在这种操作，我们就能写出不可计算的函数。

    尽管一般的不可计算性质无法表述为布尔计算，但值得注意的是，很多
    _'可计算的'_性质更容易通过 [Prop] 而非 [bool] 来表达，因为在 Coq
    中定义递归函数中会受到很大的限制。例如，下一章会展示如何用 [Prop]
    来定义“某个正则表达式可以匹配给定的字符串”这一性质。如果使用
    [bool] 来定义，就需要写一个真正的正则表达式匹配器了，这样会更加复杂，
    更难以理解，也更难以对它进行推理。

    另一方面，通过布尔值来陈述事实会带来一点重要的优势，即通过对 Coq
    中的项进行计算可以实现一些自动推理，这种技术被称为_'互映证明（Proof
    by Reflection）'_。考虑以下陈述： *)

Example even_1000 : exists k, 1000 = double k.

(** 对此命题而言，最直接的证明方式就是直接给出 [k] 的值。 *)

Proof. exists 500. reflexivity. Qed.

(** 而使用与之对应的布尔语句的证明则更加简单： *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** 有趣的是，由于这两种定义是等价的，因此我们无需显式地给出 500，
    而是使用布尔等价式来证明彼此： *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** 尽管此例的证明脚本的长度并未因此而减少，然而更大的证明通常可通过
    这种互映的方式来显著化简。举一个极端的例子，在用 Coq 证明著名的
    _'四色定理'_时，人们使用互映技巧将几百种不同的情况归约成了一个布尔计算。 *)

(** 另一点明显的不同是“布尔事实”的否定可以被直白地陈述并证明，
    只需翻转预期的布尔值结果即可。 *)

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* 课上已完成 *)
  reflexivity.
Qed.

(** 相反，命题的否定形式可能更难以掌握。 *)

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  (* 课上已完成 *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** 相等性补充了另一个例子。在涉及 [n] 和 [m] 的证明中，知道 [n =? m = true]
    通常没什么直接的帮助。然而如果我们将该语句转换为等价的 [n = m] 形式，
    则可利用该等式改写证明目标。
 *)

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* 课上已完成 *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** 我们不会详细地介绍互映技巧，然而对于展示布尔计算与一般命题的互补优势而言，
    它是个很好的例子。 *)

(** **** 练习：2 星, standard (logical_connectives)  

    以下引理将本章中讨论的命题联结词与对应的布尔操作关联了起来。 *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (eqb_neq)  

    以下定理为等价式 [eqb_eq] 的“否定”版本，
    在某些场景中使用它会更方便些（后面的章节中会讲到这方面的例子）。 *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* Fri Jul 19 00:32:20 UTC 2019 *)