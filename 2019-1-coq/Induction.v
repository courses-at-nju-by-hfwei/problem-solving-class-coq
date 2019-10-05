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

(**
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

(**
  注意观察 [assert] 对证明目标的改变。
  [assert (H : 0 + n = n)] 策略引入了一个子目标，记为 [H]。
  我们先在随后的 [{ ... }] 内给出这个子目标的证明。
  退出 [{ ... }] 后，我们又回到原来的证明目标 [(0 + n) * m = n * m]。
  此时，我们可以将 [H] 作为已知定理使用了。
*)

(**
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

(**
  [assert] 允许我们陈述一个针对证明中特定的变量的引理。
*)

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
(**
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
(** 
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

(* ################################################################# *)
(** * 形式化证明 vs. 非形式化证明 *)

(** 
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
(* ################################################################# *)
(** * 更多练习 *)

(** **** 练习：3 星, standard, recommended (mult_comm)  
    利用 [assert] 证明下述定理 [plus_swap]。(提示: 不必使用 [induction]。) *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *)
Admitted.

(** 现在我们终于可以证明乘法交换律了。你可能会用上 [plus_swap]。*)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (more_exercises) *)
(**
  注意: 以下练习题并不一定都需要使用 [induction].
  你需要通过做练习培养自己做证明时的直觉。
  直觉是非常重要的。
  
  (如果你又忘记了某些函数或者定理，请记着 [Print]、[Check] 与 [Search]。)
*)

(**
  关于布尔函数
*)
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

(**
  关于自然数之间的大小关系
*)
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

(**
  关于乘法运算。我们终于可以证明乘法分配律和乘法结合律了。
*)
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

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary : option (nat*string) := None.
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

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_commute : option (nat*string) := None.
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
  (* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_a : option (nat*string) := None.

(** 
  (b) 然而 [Theorem bin_nat_bin : forall b : bin, nat_to_bin (bin_to_nat b)] 
  并不成立。请给出反例，并解释问题所在。
*)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_b : option (nat*string) := None.

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
  (* 请在此处解答 *) Admitted.
(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_c : option (nat*string) := None.
(** [] *)
(* Fri Jul 19 00:32:19 UTC 2019 *)