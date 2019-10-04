(** * Lists: 使用结构化的数据 *)

(**
  本节介绍_'列表'(List)_数据类型。
  下一节介绍_'函数式程序设计' (Functional Programming; FP)_范型。
  
  为什么要先介绍列表呢?
  列表是函数式程序设计中的基础数据类型。
  最早的(?)的函数式程序设计语言 Lisp 的含义即是 "LISt Processor"。
*)

From LF Require Export Induction.
Module NatList.
(* ################################################################# *)
(** * 自然数序对 *)

(**
  在定义列表数据类型之前，我们先热热身，
  定义简单的自然数 _序对 (Ordered Pair)_。
  它只有一种构造方式，即将构造函数 [pair] 作用到两个自然数 [n1 n2] 上。 
*)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(**
  注意: 我们将该类型命名为 natprod，
  其中 prod 表示 _'乘积' (Product)_ 类型。
*)
Check (pair 3 5).

(**
  函数 [fst] 与 [snd] 分别用于提取有序对的第一个和第二个分量。
*)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(**
  在数学上，我们使用 [(x,y)] 表示有序对 [pair x y]。
*)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x (* [(x,y)] 即 [pair x y] *)
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(**
  由于 [natprod] 也是归纳类型 (使用 Inductive 定义)，
  因此我们可以使用 [destruct] 对 [natprod] 类型的值分情形讨论。
  又由于 [natprod] 只有一个构造函数 [pair]，
  因此使用 [destruct] 时只会产生一个子目标。
  另外，[pair] 有两个参数，
  所以可以使用 [destruct] 的 [as [f s]] 子句
  匹配并记录有序对的两个分量。 
*)
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m]. (* 仅产生一个子目标，[p] 被替换为 (n, m)。*)
  simpl. reflexivity.
Qed.

(** **** 练习：1 星, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* ################################################################# *)
(** * 自然数列表 *)

(** 
  由任意多个自然数构成的_'自然数列表'_类型
  需要使用递归来定义。
  一个自然数列表有且仅有两种构造方式:
  - 空列表是自然数列表，记为 [nil];
  - 如果 [l] 是自然数列表，[n] 是自然数，
    把 [n] 添加到 [l] 的表头，可以构成新的列表，记为 [cons n l]。
*)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(** 例如，[mylist] 是一个三元素列表。*)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(**
  对于较长的列表，要写很多的 [cons] 与括号，繁琐易错。
  以下三个 [Notation] 声明允许我们:
  - 使用 [::] 中缀操作符代替 [cons]。注意: [::] 是右结合的。
  - 使用 [[ ]] 代替 [nil]。
  - 使用单重中括号记法代替多重圆括号记法。
*)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(**
  接下来，我们定义一些常用的列表操作函数。
*)
(* ----------------------------------------------------------------- *)
(** *** Head（带默认值）与 Tail *)

(**
  [hd] 函数返回列表 [l] 的第一个元素（即“表头 (head)”）。
  由于空表没有表头，[hd] 接受另一个参数 [default] 
  作为这种特殊情况下的默认返回值。
  (后面，我们会学习一种更优雅的处理方式。)
  
  该函数的定义展示了如何对列表进行模式匹配:
  - 空列表 [nil];
  - 非空列表 [l] 可以拆分为表头 [h]
    与表尾 [t] (tail; 仍是列表) 两部分。
  这种模式匹配很常用。
*)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

(** [tl] 函数返回列表 [l] 除表头以外的部分（即“表尾 (tail)”）。*)
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.
(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(**
  [repeat] 函数接受自然数 [n] 和 [count]，
  返回一个包含了 [count] 个 [n] 的列表。
*)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
(* ----------------------------------------------------------------- *)
(** *** Length *)

(** [length] 函数返回列表 [l] 的长度。*)

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
(* ----------------------------------------------------------------- *)
(** *** Append *)

(** [app] 函数将两个列表 [l1] [l2] 联接起来。 *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** 我们常用右结合的中缀运算符 [++] 代替 [app]。*)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
(* ----------------------------------------------------------------- *)
(** *** 练习 *)

(** **** 练习：2 星, standard, recommended (list_funs) *) 
(**
  完成函数 [nonzeros]、[oddmembers] 和 [countoddmembers]
  的定义。你可以通过测试用例来理解这些函数的功能。
*)

Fixpoint nonzeros (l : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  (* 请在此处解答 *) 
Admitted.

Fixpoint oddmembers (l : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  (* 请在此处解答 *)
Admitted.

Definition countoddmembers (l : natlist) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  (* 请在此处解答 *)
Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
  (* 请在此处解答 *)
Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：3 星, advanced (alternate) *)
(**
  请完成函数 [alternate] 的定义。
  它交替地从两个列表 [l1] [l2] 取元素，
  生成一个合并后的列表。你可以通过测试用例来理解它的功能。
*)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* 请在此处解答 *)
Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* 请在此处解答 *)
Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* 请在此处解答 *)
Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* 请在此处解答 *)
Admitted.
(** [] *)
(** **** 练习：3 星, standard, recommended (more list functions) *)
(** 完成函数 [count] 的定义。*)
Fixpoint count (v : nat) (l : natlist) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 (* 请在此处解答 *)
Admitted.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 (* 请在此处解答 *)
Admitted.

(** 完成函数 [member] 的定义。*)
Fixpoint member (v : nat) (l : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_member1: member 1 [1;4;1] = true.
 (* 请在此处解答 *)
Admitted.

Example test_member2: member 2 [1;4;1] = false.
(* 请在此处解答 *)
Admitted.

(** 完成函数 [remov_one] 的定义。*)
Fixpoint remove_one (v : nat) (l : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* 请在此处解答 *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* 请在此处解答 *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* 请在此处解答 *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* 请在此处解答 *) Admitted.

(** 完成函数 [remov_all] 的定义。*)
Fixpoint remove_all (v : nat) (l : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_remove_all1:
  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* 请在此处解答 *)
Admitted.
Example test_remove_all2:
  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* 请在此处解答 *)
Admitted.
Example test_remove_all3:
  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* 请在此处解答 *)
Admitted.
Example test_remove_all4:
  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* 请在此处解答 *)
Admitted.

(** 完成函数 [subset] 的定义。*)
Fixpoint subset (l1 : natlist) (l2 : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
 (* 请在此处解答 *)
Admitted.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 (* 请在此处解答 *)
Admitted.
(** [] *)
(* ################################################################# *)
(** * 有关列表的论证 *)
(**
  接下来，我们使用之前学习过的证明策略
  论证与列表相关的定理。
*)

(** 对于定理 [nil_app]，[reflexivity] 已足够。*)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** 定理 [tl_length_pred] 需要分情况讨论。*)

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    reflexivity.
Qed.
(* ================================================================= *)
(** ** 对列表进行归纳 *)

(**
  [natlist] 是归纳定义的，
  因此，有关列表的很多定理，都可以使用数学归纳法证明。
  
  假设我们需要证明命题 [P] 对任意列表 [l] 都成立。
  我们可以对列表 [l] 作归纳:
  - [l = []]。此时，我们需要证明 [P []] 成立。
  - [l = n :: l']。
    此时，我们需要在归纳假设 [P l'] 成立的条件下，
    证明 [P l] 成立。
*)

(**
  下面使用数学归纳法证明 [app] 满足结合律。
*)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1']. (* 注意这一步 *)
  - (* l1 = [] *)
    simpl. reflexivity.
  - (* l1 = n :: l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(**
  注意: [induction l1 as [ | n l1' IHl1']] 的 [as] 从句
  对应于 [l] 的两个构造函数:
  - [ | ] 左边为空。这是因为构造函数 [nil] 不含参数，
    且在归纳证明中属于基本情形。
  - [ | ] 右边有三个参数 [n l1' IHl1']。
    前两个参数对应构造函数 [cons] 的两个参数，
    分别记录了 [l1] 的表头 [n] 与表尾 [l1']。
    另外，[IHl1'] 记录了针对 [l1'] 的归纳假设，
    即 [IHl1': (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3]。
    
  请确保你真正理解了 [induction l1 as [ | n l1' IHl1']] 
  的含义。后面，我们会看到更复杂的例子。
*)
(* ----------------------------------------------------------------- *)
(** *** 反转列表 *)

(** 函数 [rev] 将列表 [l] 反转，它的定义使用了 [app] 函数。*)

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
(** **** 练习：3 星, standard, recommended (more list functions) *)
(**
  请证明定理 [app_length]。
*)
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (** 请在此处解答 *)
Admitted.

(**
  请证明定理 [rev_length]。
  你可能需要使用 [app_length] 与 [plus_comm]。
*)
Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  (** 请在此处解答 *)
Admitted.
(** [] *)
(* ================================================================= *)
(** ** 列表练习，第一部分 *)

(** **** 练习：3 星, standard (list_exercises)  

    更多有关列表的实践： *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* 请在此处解答 *) Admitted.

(** 下面的练习有简短的解法，如果你开始发现情况已经复杂到你无法理清的程度，
    请后退一步并试着寻找更为简单的方法。 *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* 请在此处解答 *) Admitted.

(** 一个关于你对 [nonzeros] 的实现的练习： *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (eqblist)  

    填写 [eqblist] 的定义，它通过比较列表中的数字来判断是否相等。
    证明对于所有列表 [l]，[eqblist l l] 返回 [true]。 *)

Fixpoint eqblist (l1 l2 : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
 (* 请在此处解答 *) Admitted.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
(* 请在此处解答 *) Admitted.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
 (* 请在此处解答 *) Admitted.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 列表练习, 第二部分 *)

(** 下面这组简单的定理用于证明你之前关于袋子的定义。 *)

(** **** 练习：1 星, standard (count_member_nonzero)  *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 下面这条关于 [leb] 的引理可助你完成下一个证明。 *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(** Before doing the next exercise, make sure you've filled in the
   definition of [remove_one] above. *)
(** **** 练习：3 星, advanced (remove_does_not_increase_count)  *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (bag_count_sum)  

    写下一个用到函数 [count] 和 [sum] 的，关于袋子的有趣定理 [bag_count_sum]，
    然后证明它。（你可能会发现该证明的难度取决于你如何定义 [count]！） *)
(* 请在此处解答 

    [] *)

(** **** 练习：4 星, advanced (rev_injective)  

    求证 [rev] 是单射函数，即：

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

    （这个问题既可以用简单的方式解决也可以用繁琐的方式来解决。） *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_rev_injective : option (nat*string) := None.
(** [] *)
(* ################################################################# *)
(** * Options 可选类型 *)

(** 假设我们想要写一个返回某个列表中第 [n] 个元素的函数。如果我们为它赋予类型
    [nat -> natlist -> nat]，那么当列表太短时我们仍须返回某个数... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* 任意值！ *)
  | a :: l' => match n =? O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** 这种方案并不好：如果 [nth_bad] 返回了 [42]，那么不经过进一步处理的话，
    我们无法得知该值是否真的出现在了输入中。（译注：我们无法判断是什么因素让它返回了
    [42]，因为它可能是列表过短时的返回值，同时也可能是（此时列表足够长）在列表中找到的值）
    一种更好的方式是改变 [nth_bad] 的返回类型，使其包含一个错误值作为可能的结果。
    我们将此类型命名为 [natoption]。 *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

(** 然后我们可以修改前面 [nth_bad] 的定义，使其在列表太短时返回 [None]，
    在列表足够长且 [a] 在 [n] 处时返回 [Some a]。我们将这个新函数称为
    [nth_error] 来表明它可以产生带错误的结果。 *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** （在 HTML 版本中隐藏了这些老套的证明。若你想看它请点击小方格。）

    本例也是个介绍 Coq 编程语言更多细微特性的机会，比如条件表达式... *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.

 (** Coq 的条件语句和其它语言中的一样，不过加上了一点更为一般化的特性。
    由于布尔类型不是内建的，因此 Coq 实际上支持在_'任何'_带有两个构造子的，
    归纳定义的类型上使用条件表达式。当断言（guard）求值为 [Inductive]
    定义中的第一个构造子时，它被认为是真的；当它被求值到第二个构造子时，
    则被认为是假的。 *)

(** 以下函数从 [natoption] 中取出一个 [nat]，在遇到 [None] 时它将返回提供的默认值。 *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** 练习：2 星, standard (hd_error)  *)
 (** 用同样的思路修正之前的 [hd] 函数，使我们无需为 [nil] 的情况提供默认元素。  *)

Definition hd_error (l : natlist) : natoption
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* 请在此处解答 *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* 请在此处解答 *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (option_elim_hd)  *)
 (** 此练习能帮助你在新的 [hd_error] 和旧的 [hd] 之间建立联系。 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

End NatList.

(* ################################################################# *)
(** * 偏映射（Partial Maps） *)

(** 最后演示一下如何在 Coq 中定义基础的数据结构。这是一个简单的
    _'偏映射'_ 数据类型，它类似于大多数编程语言中的映射或字典数据结构。 *)

(** 首先，我们定义一个新的归纳数据类型 [id] 来用作偏映射的“键”。 *)

Inductive id : Type :=
  | Id (n : nat).

(** 本质上来说，[id] 只是一个数。但通过 [Id] 标签封装自然数来引入新的类型，
    能让定义变得更加可读，同时我们也可以灵活地按需修改它的定义。 *)

(** 我们还需要一个 [id] 的相等关系测试： *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(** **** 练习：1 星, standard (eqb_id_refl)  *)
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 现在我们定义偏映射的类型： *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(** 此声明可以读作：“有两种方式可以构造一个 [partial_map]：用构造子 [empty]
    表示一个空的偏映射，或通过将构造子 [record] 应用到一个键、一个值和一个既有的
    [partial_map] 来构造一个带“键-值”映射 的 [partial_map]。”*)

(** [update] 函数在部分映射中覆盖给定的键以取缔原值（如该键尚不存在，
    则新建其记录）。 *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** 最后，[find] 函数按照给定的键搜索一个 [partial_map]。若该键无法找到，
    它就返回 [None]；若该键与 [val] 相关联，则返回 [Some val]。
    若同一个键被映到多个值，[find] 就会返回它遇到的第一个值。 *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(** **** 练习：1 星, standard (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* 请在此处解答 *) Admitted.
(** [] *)
End PartialMap.

(** **** 练习：2 星, standard (baz_num_elts)  

    考虑以下归纳定义： *)

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(** 有_'多少'_个表达式具备类型 [baz]？（以注释说明。） *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_baz_num_elts : option (nat*string) := None.
(** [] *)

(* Fri Jul 19 00:32:19 UTC 2019 *)
