(** * Induction: 归纳证明 *)

(** 
  我们先用下面一行命令，将上一章中所有的定义都导入进来。
  在此之前，你需要先编译 [Basics.v] 得到 [Basics.vo]。
  编译方法：在 CoqIDE 中打开 [Basics.v]，
  执行 "Compile" 菜单中的 "Compile Buffer" 命令。
  
  (TODO (to ant-hengxin): How to "Make"?)
*)

From LF Require Export Basics.    
(* ################################################################# *)
(** * 归纳法证明 *)

(** 
  在上一章中，我们使用 [simpl] 证明了定理 [plus_O_n] (即，[0] 是 [+] 的左单位元)。
  下面，我们尝试使用 [simpl] 证明定理 [plus_n_O]，
  它表明 [0] 也是 [+] 的右单位元。
*)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.


(** 
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
    simpl.       (* ...不过我们又卡在这儿了 *)
Abort.

(** 
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

(** 
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

(**  
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
  induction n as [| n' IHn']. (* 讲解如下 *)
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- IHn'. (* 应用归纳假设 *)
    reflexivity.
Qed.

(** 
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

(**
  注意: 在上面的证明中，我们没有使用 [intros n]。
  当 [induction n] 会自动将 [n] 移到上下文中。
*)
(** **** 练习：2 星, standard, recommended (basic_induction)
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

(**
  我们终于可以证明加法交换律与结合律了。
*)
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

(** **** 练习：2 星, standard (double_plus)
  完成函数 [double] 的定义，它接受参数 [n]，返回 [2n]: 
*)

Fixpoint double (n:nat) : nat
  (* := 你的解答 *).
Admitted.

(** 使用 [induction] 证明 [double n = n + n]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (evenb_S) 
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

(** 和在非形式化的数学中一样，在 Coq 中，大的证明通常会被分为一系列定理，
    后面的定理引用之前的定理。但有时一个证明会需要一些繁杂琐碎的事实，
    而这些事实缺乏普遍性，以至于我们甚至都不应该给它们单独取顶级的名字。
    此时，如果能仅在需要时简单地陈述并立即证明所需的“子定理”就会很方便。
    我们可以用 [assert] 策略来做到。例如，我们之前对 [mult_0_plus]
    定理的证明引用了前一个名为 [plus_O_n] 的定理，而我们只需内联使用 [assert]
    就能陈述并证明 [plus_O_n]： *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** [assert] 策略引入两个子目标。第一个为断言本身，通过给它加前缀 [H:]
    我们将该断言命名为 [H]。（当然也可以用 [as] 来命名该断言，与之前的
    [destruct] 和 [induction] 一样。例如 [assert (0 + n = n) as H]。）
    注意我们用花括号 [{ ... }] 将该断言的证明括了起来。这样不仅方便阅读，
    同时也能在交互使用 Coq 时更容易看出该子目标何时得证。第二个目标
    与之前执行 [assert] 时一样，只是这次在上下文中，我们有了名为 [H] 的前提
    [0 + n = n]。也就是说，[assert] 生成的第一个子目标是我们必须证明的已断言的事实，
    而在第二个子目标中，我们可以使用已断言的事实在一开始尝试证明的事情上取得进展。 *)

(** 另一个 [assert] 的例子... *)

(** 举例来说，假如我们要证明 [(n + m) + (p + q) = (m + n) + (p + q)]。
    [=] 两边唯一不同的就是内层第一个子式中 [+] 的参数 [m] 和 [n] 交换了位置，
    我们似乎可以用加法交换律（[plus_comm]）来改写它。然而，
    [rewrite] 策略并不知道应该作用在 _'哪里'_。本命题中 [+] 用了三次 ，
    结果 [rewrite -> plus_comm] 只对 _'最外层'_ 起了作用... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们只需要将 (m + n) 交换为 (n + m)... 看起来 plus_comm 能搞定！*)
  rewrite -> plus_comm.
  (* 搞不定... Coq 选错了要改写的加法！ *)
Abort.

(** 为了在需要的地方使用 [plus_comm]，我们可以（为此这里讨论的 [m] 和 [n]）
    引入一个局部引理来陈述 [n + m = m + n]，之后用 [plus_comm] 证明它，
    并用它来进行期望的改写。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ################################################################# *)
(** * 形式化证明 vs. 非形式化证明 *)

(** 数学声明的成功证明由什么构成？这个问题已经困扰了哲学家数千年，
    不过这儿有个还算凑合的定义：数学命题 [P] 的证明是一段书面（或口头）的文本，
    它对 [P] 的真实性进行无可辩驳的论证，逐步说服读者或听者使其确信 [P] 为真。
    也就是说，证明是一种交流行为。

    交流活动会涉及不同类型的读者。一方面，“读者”可以是像 Coq 这样的程序，
    此时灌输的“确信”是 [P] 能够从一个确定的，由形式化逻辑规则组成的集合中
    机械地推导出来，而证明则是指导程序检验这一事实的方法。这种方法就是
    _'形式化'_ 证明。
    
(** ...而且如果你习惯了 Coq，你可能会在脑袋里逐步过一遍策略，并想象出
    每一处上下文和目标栈的状态。不过若证明再复杂一点，那就几乎不可能了。

    一个（迂腐的）数学家可能把证明写成这样： *)

(** - _'定理'_：对于任何 [n]、[m] 和 [p]，

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

      它由归纳假设直接得出。_'证毕'_。 *)
(** **** 练习：2 星, advanced, recommended (plus_comm_informal)  

    将你对 [plus_comm] 的解答翻译成非形式化证明：

    定理：加法满足交换律。

    Proof: (* 请在此处解答 *)
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_plus_comm_informal : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard, optional (eqb_refl_informal)  

    以 [plus_assoc] 的非形式化证明为范本，写出以下定理的非形式化证明。
    不要只是用中文来解释 Coq 策略！

    定理：对于任何 [n]，均有 [true = n =? n]。

    证明： (* 请在此处解答 *)

    [] *)

(* ################################################################# *)
(** * 更多练习 *)

(** **** 练习：3 星, standard, recommended (mult_comm)  

    用 [assert] 来帮助证明此定理。你应该不需要对 [plus_swap] 进行归纳。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *) Admitted.

(** 现在证明乘法交换律。（你在证明过程中可能需要定义并证明一个独立的辅助定理。
    你可能会用上 [plus_swap]。） *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (more_exercises)  

    找一张纸。对于以下定理，首先请 _'思考'_ (a) 它能否能只用化简和改写来证明，
    (b) 它还需要分类讨论（[destruct]），以及 (c) 它还需要归纳证明。先写下你的
    预判，然后填写下面的证明（你的纸不用交上来，这只是鼓励你先思考再行动！） *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  (* 请在此处解答 *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (eqb_refl)  

    证明以下定理。（把 [true] 放在等式左边可能看起来有点奇怪，不过 Coq 标准库中
    就是这样表示的，我们照做就是。无论按哪个方向改写都一样好用，所以无论我们如何
    表示定理，用起来都没问题。） *)

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (plus_swap')  

    [replace] 策略允许你指定一个具体的要改写的子项和你想要将它改写成的项：
    [replace (t) with (u)] 会将目标中表达式 [t]（的所有副本）替换为表达式 [u]，
    并生成 [t = u] 作为附加的子目标。在简单的 [rewrite] 作用在目标错误的部分上时
    这种做法通常很有用。

   用 [replace] 策略来证明 [plus_swap']，除了无需 [assert (n + m = m + n)]
   外和 [plus_swap] 一样。 *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, recommended (binary_commute)  

    回忆一下你在 [Basics] 中为练习 [binary] 编写的 [incr] 和 [bin_to_nat]
    函数。证明下图可交换。

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    也就是说，一个二进制数先自增然后将它转换为（一进制）自然数，和先将它转换为
    自然数后再自增会产生相同的结果。将你的定理命名为 [bin_to_nat_pres_incr]
    （“pres”即“preserves”的简写，意为“保持原状”）。

    在开始做这个练习之前，将你在 [binary] 练习的解中的定义复制到这里，
    让这个文件可以被单独评分。若你想要更改你的原始定义以便让此属性更易证明，
    请自便！ *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_commute : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, advanced (binary_inverse)  

    This is a further continuation of the previous exercises about
    binary numbers.  You may find you need to go back and change your
    earlier definitions to get things to work here.

    (a) First, write a function to convert natural numbers to binary
        numbers. *)

Fixpoint nat_to_bin (n:nat) : bin
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** Prove that, if we start with any [nat], convert it to binary, and
    convert it back, we get the same [nat] we started with.  (Hint: If
    your definition of [nat_to_bin] involved any extra functions, you
    may need to prove a subsidiary lemma showing how such functions
    relate to [nat_to_bin].) *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  (* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_a : option (nat*string) := None.

(** (b) One might naturally expect that we should also prove the
        opposite direction -- that starting with a binary number,
        converting to a natural, and then back to binary should yield
        the same number we started with.  However, this is not the
        case!  Explain (in a comment) what the problem is. *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_b : option (nat*string) := None.

(** (c) Define a normalization function -- i.e., a function
        [normalize] going directly from [bin] to [bin] (i.e., _not_ by
        converting to [nat] and back) such that, for any binary number
        [b], converting [b] to a natural and then back to binary yields
        [(normalize b)].  Prove it.  (Warning: This part is a bit
        tricky -- you may end up defining several auxiliary lemmas.
        One good way to find out what you need is to start by trying
        to prove the main statement, see where you get stuck, and see
        if you can find a lemma -- perhaps requiring its own inductive
        proof -- that will allow the main proof to make progress.) Don't
        define thi using nat_to_bin and bin_to_nat! *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_c : option (nat*string) := None.
(** [] *)

(* Fri Jul 19 00:32:19 UTC 2019 *)
