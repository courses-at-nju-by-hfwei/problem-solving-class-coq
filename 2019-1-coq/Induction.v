(** * Induction: 归纳证明 *)

(*
  本节依赖于 [Basics.v] (你需要先阅读它)。
  你需要先编译 [Basics.v] 得到 [Basics.vo]。
  编译方法：在 CoqIDE 中打开 [Basics.v]，
  执行 "Compile" 菜单中的 "Compile Buffer" 命令。
  
  本节介绍如何在 Coq 中做数学归纳法证明。
  数学归纳法在计算机科学中非常重要，使用非常频繁。
  记得有一次，我与一位老师聊天，我们的研究方向差别较大，
  唯一的共同点就是要经常做一些证明。
  我问，你的领域里有哪些常用的证明策略?
  他说，数学归纳法。
  
  此外，本节还会介绍两个新的证明策略:
  [injection] 与 [discriminate]。
*)

From LF Require Export Basics.    
(* ################################################################# *)
(** * 归纳法证明 *)

(*
  在上一节中，我们使用 [simpl] 证明了定理 [plus_O_n] (即，[0] 是 [+] 的左单位元)。
  下面，我们尝试使用 [simpl] 证明定理 [plus_n_O]，
  它表明 [0] 也是 [+] 的右单位元。
*)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.


(* 
  我们发现 [simpl] 不起作用。
  这是因为，[n + 0] 中的 [n] 是任意自然数，无法使用 [plus] 定义中的匹配进行化简。
  
  那么，用上一章学过的 [destruct n] 对 [n] 分情况讨论，是否可行?
*)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* So far so good... *)
  - (* n = S n' *)
    simpl. (* ...不过我们又卡在这儿了 *)
Abort. (* 终止该证明 *)

(* 
  - [n = 0] 的情形可以通过 [plus] 的第一条模式匹配完成化简。
  - 对于 [n = S n']，经过一步 [simpl] 后，
    我们还需要证明 [S n' = S (n' + 0)]。
    这意味着我们需要证明 [n' = n' + 0]。
    而这与我们一开始要证明的目标 [n = n + 0]在形式上是完全相同的，
    不同的是，此处 [n'] 比 [n] 小 1。
    这就提示我们需要使用 _'数学归纳法' (Mathematical Induction)_。
    
    在我们问题求解课程四个学期的内容中，数学归纳法经常出现，非常重要。
    甚至在大家以后的科研工作中，数学归纳法都有可能是最常用的理解问题
    与证明定理的方法。
    (请默念三遍：数学归纳法，数学归纳法，数学归纳法)
    另外，数学归纳法不仅仅是应用在自然数上的，
    而是可以应用于所有归纳定义的结构/对象。
    关于这一点，我们会在后续章节与后续课程深入学习。
*)

(* 
  我们从_'自然数上的归纳原理'_开始：
  (问卷：高中时是否学习过数学归纳法?)
  假设 [P(n)] 为关于自然数的命题。
  我们想要证明 [P] 对于所有自然数 [n] 都成立时。
  数学归纳法告诉我们，只需要：
  - 证明 [P(O)] 成立；
  - 证明对于任何 [n']，若 [P(n')] 成立，那么 [P(S n')] 也成立。

  (此处又有学生提问：怎么证明数学归纳法的正确性呢?)
  
  (答：难道你不觉得这是显然成立的吗?)
  
  (另一位学生反驳：你不是说要“怀疑一切、证明一切”吗? (TODO: 嗯，回头补上))
  
  (故作镇定：很好。那怎么证明呢? 这个问题我们还是先留给大家思考吧。
  后续课程中我们还有机会回到这个问题上来。)
*)

(*  
  Coq 通过应用 [induction] 策略把待定目标 [forall n : nat, n = n + 0]
  分为两个子目标:
  - 基础情况: [n = 0]。此时，我们需要证明 [P(0)]，即 [0 = 0 + 0] 成立。
  - 归纳步骤: [n = S n']。
    此时，我们有归纳假设 [P(n')] 成立，即 [n' = n' + 0] 成立。
    我们需要在归纳假设 [P(n')] 成立的基础上，证明 [P(n)] 成立，
    即证明 [P(S n')] 成立，
    也就是 [S n' = S n' + 0] 成立。
    基本的证明方法就是将对 [P(S n')] 的证明
    化归 (Reduce) 到可以直接应用归纳假设 [P(n')] 的情况。
*)

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn']. (* 下面会详细解释这句话 *)
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- IHn'. (* 应用归纳假设 [IHn'] *)
    reflexivity.
Qed.

(* 
  根据上面的分析，对自然数 [n] 应用 [induction] 策略，
  会产生两个子目标。
  就像使用 [destruct] 做分情形分析一样，在 [induction] 中，
  我们使用 [as [ | ]] 表达基本情况与归纳步骤。
  - 在基本情况中，[n = 0]。不需要额外参数。
  - 在归纳步骤，[n = S n']。我们需要引入额外参数代表 [n']。
  需要特别注意的是，我们还使用 IHn' 记录了归纳假设。
*)

Theorem minus_diag : forall n : nat,
  minus n n = 0.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(*
  注意: 在上面的证明中，我们没有使用 [intros n]。
  当 [induction n] 会自动将 [n] 移到上下文中。
*)
(* **** 练习：2 星, standard, recommended (basic_induction)
    使用 [induction] 完成以下证明。你可能需要使用之前证明的定理。
    记住 [Print]、[Search]。
*)

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* 请在此处解答 *)
Admitted.

(* 我们终于可以证明加法交换律与结合律了。*)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* **** 练习：2 星, standard (double_plus)
  完成函数 [double] 的定义，它接受参数 [n]，返回 [2n]
  (你可以将 [Basics.v] 的定义拷贝过来): 
*)

Fixpoint double (n:nat) : nat
  (* := 你的解答 *).
Admitted.

(* 使用 [induction] 证明 [double n = n + n]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* **** 练习：2 星, standard, optional (evenb_S) 
  证明下述关于 [evenb] 的定理。
*)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* ################################################################# *)
(** * 证明里的证明 *)

(*
  关于 [induction]，我们暂时介绍这么多。
  后面，我们还会回到这个主题。
  
  下面，我们介绍一个在做证明时经常会碰到的情况:
  一个证明会依赖于其它结论，但是这个结论可能很简单，或者缺乏普遍性，
  不值得我们专门为之引入一个定理。
  这时，Coq 允许我们使用 [assert] 策略将该结论嵌入 (inline) 在大的证明结构中。 
*)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  (* 当然，我们可以直接使用 [simpl.]。这里仅做演示之用。*)
  assert (H: 0 + n = n). { reflexivity. } 
  rewrite H.
  reflexivity.
Qed.

(*
  注意观察 [assert] 对证明目标的改变。
  [assert (H : 0 + n = n)] 策略引入了一个子目标，记为 [H]。
  我们先在随后的 [{ ... }] 内给出这个子目标的证明。
  退出 [{ ... }] 后，我们又回到原来的证明目标 [(0 + n) * m = n * m]。
  此时，我们可以将 [H] 作为已知定理使用了。
*)

(*
  [assert] 还有一个特别的用处，我们举例说明。
  假设我们要证明 [(n + m) + (p + q) = (m + n) + (p + q)]。
  似乎我们可以直接使用加法交换律 [plus_comm] 将等号左边的 [(n + m)] 
  改写为等号右边的 [(m + n)]。
  但是，这里有6个加号，Coq 的 [rewrite plus_comm] 并没有聪明到
  知道我们想对哪个加号应用加法交换律。
  实际上，它将 [rewrite plus_comm] 作用在了最外层的加号上。
*)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们希望将 (m + n) 改写为 (n + m) *)
  rewrite -> plus_comm.
  (* 但是，Coq 将 [plus_comm] 应用到了最外层的加号上 *)
Abort.

(* [assert] 允许我们陈述一个针对证明中特定的变量的引理。*)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). (* 针对 [n] 与 [m] *)
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. 
  reflexivity.
Qed.

Print plus_comm.
(*
  在后面章节，我们将会看到，这个证明中的第2到第4行，可以用一条语句代替：
  [rewrite (plus_comm n m).]。
  回顾 [plus_comm] 定理:
  [forall n m : nat, n + m = m + n]。
  我们可以将该定理看成接受两个自然数的函数。
  给定 [n] 与 [m]，[plus_comm n m] 就是加法交换律在 [n] 与 [m] 上的实例化。
  
  哦，定理是函数? 那就可以做计算了?
  嗯，没错。关于这个话题，我们先点到为止。后面我们还会回来。
*)

(** **** 练习：2 星, standard, optional (plus_swap') *)
(* 
  除了 [assert]，我们还可以使用 [replace] 策略证明上述定理。
  [replace (t) with (u)] 会将目标中 [t] 的所有 _'出现' (occurrences)_替换为 [u],
  并生成子目标 [t = u]。
  请根据上面的介绍，尝试使用 [replace] 重新证明 [plus_swap]。
*)
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (sum_to_equation) *)
Print sum_to.

(*
  TODO: (@ant-hengxin) 该练习还有问题，暂时不需要完成。
  等待 @ant-henxin 修复。
  
  请证明 Gauss 所发现的求和公式 ([sum_to_equation])
  : 1 + 2 + ... + n = 1/2 n (n+1).
  
  你可能需要用到下面的引理。
*)

Lemma sum_helper : forall n : nat,
  2 * sum_to (S n) = 2 * (S n) + 2 * (sum_to n).
Proof. (* 目前，我们还无法证明该引理。我们直接接受它。*) Admitted.

Theorem sum_to_equation : forall n : nat,
  2 * (sum_to n) = n * (n + 1).
Proof. Admitted.
(* ################################################################# *)
(** * 形式化证明 vs. 非形式化证明 *)

(*
  在初中，我们就开始写数学证明了。
  但是，什么是证明?
  我们好像从来没有给证明本身下过定义?
  
  关于这个问题的答案，我们把它留给你们的数理逻辑老师。
  让人惊讶的是，为证明下定义也不过是最近一百年的事情。
  同样让人惊讶的是，我们的经验表明，不知道证明的定义也并不妨碍我们做证明。

  在 Coq 里，我们需要写机器可以检验的 _'形式化证明' (Formal Proof)_，
  而大多数时候，我们写的是 _'非形式化证明' (Informal Proof)_。
  如下所示。
*)

(* - _'定理'_：对于任何 [n]、[m] 和 [p]，

      n + (m + p) = (n + m) + p.

    _'证明'_：对 [n] 使用归纳法。

    - 首先，设 [n = 0]。我们必须证明

        0 + (m + p) = (0 + m) + p.

      此结论可从 [+] 的定义直接得到。

    - 然后，设 [n = S n']，其中

        n' + (m + p) = (n' + m) + p.

      我们必须证明

        (S n') + (m + p) = ((S n') + m) + p.

      根据 [+] 的定义，该式可写成

        S (n' + (m + p)) = S ((n' + m) + p),

      它由归纳假设直接得出。_'证毕'_。 
*)
(* ################################################################# *)
(** * 更多练习 *)

(* **** 练习：3 星, standard, recommended (mult_comm)  
    利用 [assert] 证明下述定理 [plus_swap]。(提示: 不必使用 [induction]。) *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *)
Admitted.

(* 现在我们终于可以证明乘法交换律了。你可能会用上 [plus_swap]。*)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (more_exercises) *)
(*
  注意: 以下练习题并不一定都需要使用 [induction].
  你需要通过做练习培养自己做证明时的直觉。
  直觉是非常重要的。
  
  (如果你又忘记了某些函数或者定理，请记着 [Print]、[Check] 与 [Search]。)
*)

(* 关于布尔函数 *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* 请在此处解答 *)
Admitted.

(* 关于自然数之间的大小关系 *)
Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem leb_refl : forall n : nat,
  true = (n <=? n).
Proof.
  (* 请在此处解答 *)
Admitted.

Print eqb.
Theorem zero_nbeq_S : forall n : nat,
  0 =? (S n) = false.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem S_nbeq_zero : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  (* 请在此处解答 *)
Admitted.

(* 关于乘法运算。我们终于可以证明乘法分配律和乘法结合律了。*)
Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* ################################################################# *)
(** * 变换归纳法则 *)

(*
  当命题涉及多个归纳 (Inductive) 类型或者同一个归纳类型的多个变量时，
  使用数学归纳法的首要任务就是要确定对哪个变量做归纳。
  比如下面的定理 [double_injective]，
  它说明 [double] 是单射函数
  (你应该已经在 [Basics.v] 中定义了 [double]。
   为了避免冲突，我们使用 Module 机制)。
  该定理涉及两个自然数类型变量 [n] 和 [m]。
  我们需要对哪个变量进行归纳呢?
*)

Module InductionPlayground.
Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective: forall n m,
  double n = double m -> n = m.

(*
   一种选择是对 [n] 做归纳。
   比如，以 [intros n. induction n as [ | n' IHn'].] 开始证明。
   恭喜你，这个选择是明智的。
   
   我们来看一下完整的证明。
   请注意观察每一步后证明目标与证明上下文的变化，
   并扪心自问: 你 (对，就是你) 真得真得真得理解了吗?
   
   此外，在这个证明中，我们需要用到新的证明策略
   [injection] 与 [discriminate]。
*)

Proof.
  intros n. induction n as [ | n' IHn'].
  - (* n = 0 *) 
    intros m eq. simpl in eq.
    destruct m as [ | m'] eqn:E.
    + (* E : m = 0 *)
      reflexivity.
    + (* E : m = S m' *)
      simpl in eq. discriminate eq. (* 下面解释这句话 *)
  - (* n = S n' *)
    simpl. intros m eq.
    destruct m as [ | m'] eqn:E.
    + (* E : m = 0 *) simpl in eq. discriminate eq.
    + (* E : m = S m' *) 
      apply f_equal. (* TODO: 在之前解释 [f_equal] *)
      apply IHn'.
      simpl in eq.
      injection eq as H. (* 下面解释这句话 *)
      apply H.
Qed.

(*
  如果你已经扪心自问过了 (并且得到了肯定的答复)，
  那么你就已经懂得了如何在 Coq 中做基本的数学归纳法证明。
  
  下面，我们打个岔，先介绍一下上述证明中用到的两个新的证明策略:
  [injection] 与 [discriminate]。
  
  先讲 [discriminate]。
  (discriminate，区分，辨别也。在区分什么? 马上揭晓。)
  
  在证明进行到第一处 [discriminate eq.] 时，
  证明目标是 [0 = S m']，[eq] 为 [eq : 0 = S (S (double m'))]。
  我们发现此时的证明目标 [0 = S m'] 是假的。
  因为只有假才能蕴含假，所以证明上下文(合起来)应该也是假的。
  [discriminate eq.] 的效果就是告诉 Coq:
  [eq : 0 = S (S (double m'))] 是假的，因此目标得证。
  作为一位不苟言笑的老大哥，Coq 要检查 
   [eq : 0 = S (S (double m'))] 确实是假的。
  那它怎么知道这个是假的呢?
  我们需要回到自然数类型的定义。
  
  Inductive nat : Type :=
    | O
    | S (n : nat).
*)
Print nat.
(*
  观察 CoqIDE 的右下角输出，忽略 (: Set)，
  你会发现它与我们在 [Basics.v] 中的定义不太一样。
  不过，这只是"披了件外衣"，
  它仍然表示: O 与 [S] 是 "唯二" 的构造函数。
  
  不仅如此!
  所有归纳定义的背后还隐藏着两个"秘密":
  - 每个构造函数都是单射函数。
  - 不同的构造函数是不相交的。
  
  对自然数类型而言，这意味着:
  - 构造函数 [S] 是单射函数。
    也就是说，如果 S n = S m，则 n = m。
  - [O] 与 [S] 是不相交的。
    也就是说，[O] 与 [S n] 是不相同的 ([n] 为任意自然数)。
*)

(*
  回到上面的证明。
  我们有 [eq : 0 = S (S (double m'))]。
  Coq 就是根据 [O] 与 [S] 的不相交性判定 [eq] 为假的。
  这种证明策略称为 [discriminate]。
*)

(*
  接下来介绍 [injection] 证明策略。
  [injection]，"injective" 单射。
  你是否猜到了它和什么有关?
  是的，它用到了上面所说的第一个"秘密"。
  
  当上面的证明进行到 [injection eq as H.] 时，
  证明目标是 [double n' = double m']，
  [eq] 为 [eq : S (S (double n')) = S (S (double m'))]。
  因为 [S] 是单射函数，
  所以我们可以推出 [S (double n') = S (double m')]，
  进一步推出 [double n' = double m']。
  [injection eq] 的效果就是根据 [S] 的单射性质作出上面的推导，
  得到 [double n' = double m']。
  [injection eq as H.] 会将得到的 [double n' = double m']
  命名为 [H]，作为新的证明上下文。
  有了 [H]，[apply H.] 就证明了目标。
  
  (如果仅使用 [injection eq.]，没有 [as H]，
  那么推导得到的 [double n' = double m'] 会作为前件插入到
  证明目标中。
  也就是说，证明目标会变成 
  [double n' = double m' -> double n' = double m']。
  这样的话，我们还需要使用 [intros H] 将它引入到上下文中。) 
*)

(*
  好了，对 [injection] 与 [discriminate] 的介绍到此为止。
  我们已经知道了如何通过对 [n] 做归纳证明 [double_injective]。
  
  现在，假设你选择对 [m] 做归纳，并且以
  [intros n m. induction n as [ | n' IHn'].] 开始证明 ... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq. (* [simpl in eq] 不必要 *)
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.

(**
  现在，回到我们的主题上来。
  
  证明进行到此，我们的待证目标变成 [n' = m']。
  我们的归纳假设 [IHn'] 是 
  [IHn' : double n' = double (S m') -> n' = S m']。
  
  但是，从这个归纳假设，我们无法证明 [n' = m']:
  归纳假设的结论部分是 [n' = S m']，而不是 [n' = m']。
  
  证明进入死胡同。
  沮丧。
  终止。
*)
Abort.

(**
  为什么会这样呢? 
  [n] 与 [m] 在定理 [double_injective] 中难道不是对称的吗?
  它们的作用难道不是一样的吗?
  为什么对 [n] 做归纳可以很顺利，对 [m] 做归纳就进入了死胡同呢?
  
  我们不妨回头比较一下两种做法在执行完 [induction] 策略后产生的证明状态。
  - 第一种做法: [intros n. induction n as [ | n' IHn'].]
  - 第二种做法: [intros n m. induction m as [ | m' IHm'].]
*)

(* 
  发现问题了吗?
  
  问题很严重。
  
  TODO: 继续……
  问题在于，我们在调用归纳假设的地方已经将 [m] 引入了上下文中 --
    直观上，我们已经告诉了 Coq“我们来考虑具体的 [n] 和 [m]...”，
    而现在必须为这些_'具体的'_ [n] 和 [m] 证明 [double n = double m]，
    然后才有 [n = m]。

    下一个策略 [induction n] 告诉 Coq：我们要对 [n] 归纳来证明该目标。
    也就是说，我们要证明对于_'所有的'_ [n]，命题

      - [P n] = "if [double n = double m], then [n = m]"

    成立，需通过证明

      - [P O]

        （即，若“[double O = double m] 则 [O = m]”）和

      - [P n -> P (S n)]

        （即，若“[double n = double m] 则 [n = m]”蕴含“若
        [double (S n) = double m] 则 [S n = m]”）来得出。

    如果我们仔细观察第二个语句，就会发现它说了奇怪的事情：即，对于一个_'具体的'_
    [m]，如果我们知道

      - “若 [double n = double m] 则 [n = m]”

    那么我们就能证明

       - “若 [double (S n) = double m] 则 [S n = m]”。

    要理解为什么它很奇怪，我们来考虑一个具体的 [m] --
    比如说，[5]。该语句就会这样说：如果我们知道

      - [Q] = “若 [double n = 10] 则 [n = 5]”

    那么我们就能证明

      - [R] = “若 [double (S n) = 10] 则 [S n = 5]”。

    但是知道 [Q] 对于证明 [R] 来说并没有任何帮助！（如果我们试着根据 [Q]
    证明 [R] from [Q]，就会以“假设 [double (S n) = 10]..”这样的句子开始，
    不过之后我们就会卡住：知道 [double (S n)] 为 [10] 并不能告诉我们
    [double n] 是否为 [10]，因此 [Q] 是没有用的。） *)

(** 当 [m] 已经在上下文中时，试图对 [n] 进行归纳来进行此证明是行不通的，
    因为我们之后要尝试证明涉及_'每一个'_ [n] 的命题，而不只是_'单个'_ [m]。 *)

(** 对 [double_injective] 的成功证明将 [m] 留在了目标语句中 [induction]
    作用于 [n] 的地方：*)

Theorem double_injective_revisited : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.

(* 注意，此时的证明目标和归纳假设是不同的：证明目标要求我们证明更一般的事情
    （即，为_'每一个'_ [m] 证明该语句），而归纳假设 [IH] 相应地更加灵活，
    允许我们在应用归纳假设时选择任何想要的 [m]。 *)

    intros m eq.

(** 现在我们选择了一个具体的 [m] 并引入了假设 [double n = double m]。
    由于我们对 [n] 做了情况分析，因此还要对 [m] 做情况分析来保持两边“同步”。 *)

    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.

(** 0 的情况很显然： *)

      discriminate eq.

    + (* m = S m' *)
      apply f_equal.

(** 到这里，由于我们在 [destruct m] 的第二个分支中，因此上下文中涉及到的 [m']
    就是我们开始讨论的 [m] 的前趋。由于我们也在归纳的 [S] 分支中，这就很完美了：
    如果我们在归纳假设中用当前的 [m']（此实例由下一步的 [apply] 自动产生）
    实例化一般的 [m]，那么 [IHn'] 就刚好能给出我们需要的来结束此证明。 *)

      apply IHn'. injection eq as goal. apply goal. Qed.
End InductionPlayground.

(** What you should take away from all this is that we need to be
    careful, when using induction, that we are not trying to prove
    something too specific: To prove a property of [n] and [m] by
    induction on [n], it is sometimes important to leave [m]
    generic. *)

(** 以下练习需要同样的模式。 *)

(** **** 练习：2 星, standard (eqb_true)  *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, advanced (eqb_true_informal)  

    给出一个详细的 [eqb_true] 的非形式化证明，量词要尽可能明确。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** 在 [induction] 之前做一些 [intros] 来获得更一般归纳假设并不总是奏效。
    有时需要对量化的变量做一下_'重排'_。例如，假设我们想要通过对 [m]
    而非 [n] 进行归纳来证明 [double_injective]。 *)

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
        (* 和前面一样，又卡在这儿了。 *)
Abort.

(** 问题在于，要对 [m] 进行归纳，我们首先必须对 [n] 归纳。
    （如果我们不引入任何东西就执行 [induction m]，Coq 就会自动为我们引入 [n]！） *)

(** 我们可以对它做什么？一种可能就是改写该引理的陈述使得 [m] 在 [n] 之前量化。
    这样是可行的，不过它不够好：我们不想调整该引理的陈述来适应具体的证明策略！
    我们更想以最清晰自然的方式陈述它。 *)

(** 我们可以先引入所有量化的变量，然后_'重新一般化（re-generalize）'_
    其中的一个或几个，选择性地从上下文中挑出几个变量并将它们放回证明目标的开始处。
    用 [generalize dependent] 策略就能做到。*)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* 现在 [n] 回到了目标中，我们可以对 [m] 进行归纳并得到足够一般的归纳假设了。 *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(** 我们来看一下此定理的非形式化证明。注意我们保持 [n]
    的量化状态并通过归纳证明的命题，对应于我们形式化证明中依赖的一般化。

    _'定理'_：对于任何自然数 [n] 和 [m]，若 [double n = double m]，则 [n = m]。

    _'证明'_：令 [m] 为一个 [nat]。我们通过对 [m] 进行归纳来证明，对于任何 [n]，
        若 [double n = double m]，则 [n = m]。

      - 首先，设 [m = 0]，而 [n] 是一个数使得 [double n = double m]。
        我们必须证明 [n = 0]。

        由于 [m = 0]，根据 [double] 的定义，我们有 [double n = 0]。此时对于 [n]
        需要考虑两种情况。若 [n = 0]，则得证，因为 [m = 0 = n]，正如所需。
        否则，若对于某个 [n'] 有 [n = S n']，我们就会导出矛盾：根据 [double]
        的定义，我们可得出 [double n = S (S (double n'))]，但它与 [double n = 0]
        相矛盾。

      - 其次，设 [m = S m']，而 [n] 同样是一个数使得 [double n = double m]。
        我们必须证明 [n = S m']，根据归纳假设，对于任何数 [s]，若
        [double s = double m']，则 [s = m']。

        根据 [m = S m'] 的事实以及 [double] 的定义我们有 [double n = S (S (double m'))]。
        此时对于 [n] 需要考虑两种情况。

        若 [n = 0]，则根据 [double n = 0] 的定义会得出矛盾。

        因此，我们假设对于某个 [n']，有 [n = S n']，同样根据 [double]
        的定义，我们有 [S (S (double n')) = S (S (double m'))]，它可通过反演
        [double n' = double m'] 得出。以 [n'] 实例化归纳假设允许我们得出
        [n' = m'] 的结论，显然 [S n' = S m']。因此 [S n' = n] 且 [S m' = m]，
        此即我们所欲证。 [] *)

(*
(* 在结束本节去做习题之前，我们先稍微跑个题，使用 [eqb_true]
    来证明一个标识符的类似性质以备后用： *)

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.
*)

(** **** 练习：3 星, standard (binary)
  下面这道题目可以检验你是否掌握了本节(以及上一节)的主要内容。
  不要怕。正是这些让你感到有些困难的题目在悄悄地锻炼你的能力。
  
  我们考虑自然数的一种 _'二进制' (Binary)_ 表示法：
  一个二进制数是由构造子 (即，构造函数) [A] (表示 0) 与 [B] (表示 1)
  组成的序列，且该序列以构造子 [Z] 结束。
  (能理解这句话吗? 我实在不知道该怎么表达了。
  它的英文是：“treating a binary number as a sequence of constructors [A] and [B] (representing 0s and 1s), terminated by a [Z].”。
  Help me if you can!)
  
  在我们定义的 _'一进制' (unary)_ [nat] 中，
  一个一进制数是由构造子 [S] 组成的序列，且该序列以构造子 [O] 结束。

  看下面的例子 (注意，低位 (low-order bit) 在左，高位 (high-order bit) 在右)：


        decimal            binary                           unary
           0                   Z                              O
           1                 B Z                            S O
           2              A (B Z)                        S (S O)
           3              B (B Z)                     S (S (S O))
           4           A (A (B Z))                 S (S (S (S O)))
           5           B (A (B Z))              S (S (S (S (S O))))
           6           A (B (B Z))           S (S (S (S (S (S O)))))
           7           B (B (B Z))        S (S (S (S (S (S (S O))))))
           8        A (A (A (B Z)))    S (S (S (S (S (S (S (S O)))))))
  
*)

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

(** (a) 请给出递增函数 [incr] 与转换函数 [bin_to_nat] 的定义。 *)

Fixpoint incr (m:bin) : bin
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(**    
  (b) 为 [incr] 与 [bin_to_nat] 编写单元测试 (使用 [Example]) 并给出证明。
  你至少需要编写单元测试用例测试 [incr] 与 [bin_to_nat] 的可交换性。
*)

(* 请在此处解答 *)
(** [] *)

(** **** 练习：3 星, standard, recommended (binary_commute)  
  在上一个练习中，你已经测试过 [incr] 与 [bin_to_nat] 的可交换性，
  如下图所示 (这种图被称为 _'交换图' (Commutative Digram???)_，
  在以后的课程中还会遇到)。

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

  现在，请将 [incr] 与 [bin_to_nat] 的可交换性表达成一个定理，
  名为 [bin_to_nat_preserve_incr]。
  你能给出它的证明吗?
*)

(* 请在此处解答 *)
(** [] *)
(** **** 练习：5 星, advanced (binary_inverse) *)  
(** (a) 完成函数 [nat_to_bin] 的定义，它将自然数 [n] 转换为二进制形式。*)

Fixpoint nat_to_bin (n : nat) : bin
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(**
  证明如下定理。它的含义很直观，你应该能猜得到。
*)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  (* 请在此处解答 *)
Admitted.

(** 
  (b) 然而 [Theorem bin_nat_bin : forall b : bin, nat_to_bin (bin_to_nat b)] 
  并不成立。请给出反例，并解释问题所在。
*)

(* 请在此处解答 *)

(**
  (c) 为了修复上述定理，我们先定义一个函数 [normalize]，
  它接受一个 [bin]，并将其 "正规化"。
  请完成函数 [normalize] 的定义，使得定理 [bin_nat_bin_eqb_normalize] 成立。
  注意: 你可能需要先证明一些引理。
*)

Fixpoint normalize (b : bin) : bin
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
          
Theorem bin_nat_bin_eqb_normalize : 
  forall b : bin, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* Fri Jul 19 00:32:19 UTC 2019 *)