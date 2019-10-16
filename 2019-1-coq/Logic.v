(** * Logic: Coq 中的逻辑系统 *)

(** 
  本节依赖于 [Basics.v] (你需要先阅读它)。
  你需要先编译 [Basics.v] 得到 [Basics.vo]。
  编译方法：在 CoqIDE 中打开 [Basics.v]，
  执行 "Compile" 菜单中的 "Compile Buffer" 命令。
  
  (TODO (@ant-hengxin): How to "Make"?)
*)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Basics.

(**
  "逻辑是不可战胜的，因为反对逻辑还得使用逻辑。"
  (Logic is invincible because in order to combat logic 
  it is necessary to use logic.) By Pierre Boutroux.
  
  本节介绍一阶谓词逻辑 
  (说它是一阶谓词逻辑并不严格，我们以后讨论。) 
  的 _'自然推理系统'_ (Natural Deduction System)。
  系统，封闭之结构也;
  推理，证明之路径也;
  自然，“无他，但手熟尔”。
  这个推理系统，我们基本每天都在使用 (或者误用)。
  本节只不过是告诉你如何在 Coq 中使用这个推理系统证明定理 
  (有 Coq 盯着你，你就再也不会误用它们了)。
  
  在一阶谓词逻辑中，我们会考虑各种 _'命题'_ (Proposition)，包括
  _'合取'_ (Conjunctive) 命题、_'析取'_ (Disjunctive) 命题、
  _'否定'_ (Negative) 命题、_'蕴含_ (Implication)' 命题、
  _'等价'_ (Equivalence) 命题、_'相等性'_ (Equality) 命题、
  _'存在'_ (Existence) 命题以及 _'全称'_ (Forall) 命题。 
  
  关于逻辑，首先需要介绍的一个概念就是 _'命题'_ (Proposition)。
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
  _'是'_一个命题与该命题_'为真'_ (或者说，_'可被证明'_ (Provable)) 是两回事。
  后者是计算机科学与数理逻辑的重要研究对象。 
*)

(**
  在 Coq 中，命题是 _'一等对象'_ (First-Class Object)'，
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
  实际上，这类函数定义了其参数的某种_'性质'_ (Property)。 
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
  函数 [injective] 定义了一个函数是否是 _'单射函数'_ (Injective Functions)。
  定义中的 "[{A B}]" 表示 [A]、[B] 是两个参数化类型，
  我们会在后续介绍，这里可以当作它们不存在。
*)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

(** 
  相等关系运算符 [=] 也是一个返回 [Prop] 的函数。
  表达式 [n = m] 只是 [eq n m] 的 _'语法糖'_ (Syntactic Sugar)。
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
  自然推理系统中的规则有很好的对称性。
  它为每个逻辑联结词引入两个规则，
  一个是 introduction 规则，一个是 elimination 规则。
  introduction 规则用于证明含有相应逻辑联结词的目标，
  而 elimination 规则用于消除前提中含有的相应逻辑联结词。
  
  强烈建议: 请结合以下资料阅读并练习本节后续内容。
  - https://www.cs.cornell.edu/courses/cs3110/2013sp/lectures/lec15-logic-contd/lec15.html
  - https://leanprover.github.io/logic_and_proof/natural_deduction_for_propositional_logic.html
  - https://leanprover.github.io/logic_and_proof/natural_deduction_for_first_order_logic.html 
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

(** **** 练习：2 星, standard (and_exercise) *)
(** TODO: (@ant-hengxin) 用到了后面才介绍的 [discriminate] 策略。*)

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
  命题 [A \/ B] 表示 [A] 与 [B] 的 _'析取'_ (即 _逻辑或_)。
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
  这实际上是 [->-elimination] 规则，也就是 _'modus ponens'_ 规则，
  后面会有介绍。
*)

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. (* 对 [HP] _'正向'_ (Forward) 应用蕴含式。*)
  destruct HP.
Qed.

(**
  上面的证明使用了 [apply] 策略的第三种用法:
  [HNP] 是蕴含式 [HNP : P -> False]。
  [HP] 是 [HP : P]。
  注意到 [HP] 与 [HNP] 的前件相同，
  此时，[apply HNP in HP] 是在正向应用 modus ponens 规则:
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
(** ** 蕴含 *)
(**
  命题 [A -> B] 表示命题 [A] 蕴含命题 [B]。
  [A -> B] 为真当且仅当 [A] 为假或者 [A]、[B]均为真。
  我们已经见识过一些涉及蕴含的命题与证明了。
  这里，我们从自然推理系统的角度重新审视之前使用的证明策略。
    
  要证明 [A -> B]，我们通常将 [A] 作为假设加入到上下文中，
  然后在假设 [A] 成立的前提下，证明 [B]。
  这就是对 "->-intro" 规则的逆向使用。
  注意: 当我们应用该规则时，新加入的假设 [A] 被 discharged 了。
  (discharged，"放电"? "释放"? "撤销"? 我找不到合适的译法。大家意会吧。)
*)

Theorem ABA : forall A B : Prop, A -> (B -> A).
Proof.
  intros A B HA HB.
  apply HA.
Qed.

(**
  如果当前证明上下文中存在形如 [A -> B] 的前提 [H : A -> B]，
  并且存在前提 [Q : A]，那么我们可以使用 [apply H in Q]，得到 [B]。
  这就是 "->-elimination" 规则，
  也就是常说的 _分离规则_ (modus ponens; MP)。
*)

Theorem ABBC : forall A B C : Prop,
  ((A -> B) /\ (B -> C)) -> (A -> C).
Proof.
  intros A B C [HAB HBC].
  intros HA.
  apply HAB in HA.
  apply HBC in HA.
  apply HA.
Qed.

(** **** 练习：1 星, standard, recommended (implies) *)
Theorem A_or_BA : forall A B : Prop,
  (A \/ (B /\ A)) -> A.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem ABC : forall A B C : Prop, (* 起名字好难啊 *)
  ((A -> (B -> C)) /\ B) -> (A -> C).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
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

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *) intros H. rewrite H. intros H'.
    discriminate H'. (* 下面解释该行*)
Qed.

(**
  在上面证明的最后，我们使用了 [discriminate H'] 完成证明。
  此时，[H': false = true]。[false] 与 [true] 是 [bool] 类型的两个构造函数。
  在归纳定义中，不同的构造函数构造出的值一定是不同的。
  如果上下文出现类似 [H'] 的假设，则可以立即使用 [discriminate] 完成证明。
  关于 [discriminate] 的详细介绍，我们留到 [Induction.v] 中。 
*)

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
  [exists] 是 _'存在量词'_。
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
  会被 discharged 掉。)
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
  在 "ConsLogic.v" 中，我们会给出答案
  (TODO: (@ant-hengxin) 什么时候写这一节呢?)。
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
  
  在证明涉及全称量词的命题 [forall x : T, P] 时，
  我们通常的做法是: 先任取 [x]，然后证明对于这个任取的 [x]，[P] 成立。
  这就是在使用 "forall-intro" 规则。
  比如我们之前证明过的 [and_elim_left].
*)
Lemma and_elim_left' : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q. (* 逆用 "forall-intro" 规则: 任取 [P] 与 [Q] *)
  intros [HP HQ].
  apply HP.
Qed.

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

(** **** 练习：2 星, standard (logical_connectives)  

    以下引理将本章中讨论的命题联结词与对应的布尔操作关联了起来。 *)

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* Fri Jul 19 00:32:20 UTC 2019 *)