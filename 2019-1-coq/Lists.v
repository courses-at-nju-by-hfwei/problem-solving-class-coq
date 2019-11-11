(** * Lists: 基本数据类型 *)

(**
  本节介绍 _'列表'_ (List) 数据类型。
  下面两节介绍 _'函数式程序设计'_ (Functional Programming; FP) 范型。
  
  为什么要先介绍列表呢?
  因为列表是函数式程序设计中最基本的数据类型。
  最早的函数式程序设计语言之一 Lisp 的含义即是 "LISt Processor"。
  
  除了列表，本节还将介绍计算机科学中最常见、最漂亮的数据类型: 
  _'树'_ (Tree 🌲)。
  "Trees sprout up just about everywhere in computer science.
  --- Donald Knuth"
  
  (在计算机科学中，树的根在顶部，叶子在底部，
  这是计算机科学对自然科学作出的巨大贡献。)
*)

(** 
  本节依赖于 [Induction.v] (你需要先阅读它)。
  你需要先编译 [Induction.v] 得到 [Induction.vo]。
  编译方法：在 CoqIDE 中打开 [Induction.v]，
  执行 "Compile" 菜单中的 "Compile Buffer" 命令。
*)

From LF Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * 自然数序对 *)

(**
  在定义列表数据类型之前，我们先热热身，
  定义简单的自然数 _'序对'_ (Ordered Pair)。
  它只有一种构造方式，即将构造函数 [pair] 作用到两个自然数 [n1 n2] 上。 
*)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(**
  注意: 我们将该类型命名为 natprod，
  其中 prod 表示 _'乘积'_ (Product) 类型。
*)
Check (pair 3 5).

(** 函数 [fst] 与 [snd] 分别用于提取有序对的第一个和第二个分量。*)

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

(** 在数学上，我们使用 [(x,y)] 表示有序对 [pair x y]。*)

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
  由任意多个自然数构成的 _'自然数列表'_ 类型
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

(** 接下来，我们定义一些常用的列表操作函数。*)

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
(** 请完成函数 [count] 的定义。*)
Fixpoint count (v : nat) (l : natlist) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. (* 请在此处解答 *) Admitted.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. (* 请在此处解答 *) Admitted.

(** 请完成函数 [member] 的定义。*)
Fixpoint member (v : nat) (l : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_member1: member 1 [1;4;1] = true.
Proof. (* 请在此处解答 *) Admitted.

Example test_member2: member 2 [1;4;1] = false.
Proof. (* 请在此处解答 *) Admitted.

(** 请完成函数 [remov_one] 的定义。*)
Fixpoint remove_one (v : nat) (l : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. (* 请在此处解答 *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. (* 请在此处解答 *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. (* 请在此处解答 *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* 请在此处解答 *) Admitted.

(** 完成函数 [remov_all] 的定义。*)
Fixpoint remove_all (v : nat) (l : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_remove_all1:
  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. (* 请在此处解答 *) Admitted.

Example test_remove_all2:
  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. (* 请在此处解答 *) Admitted.

Example test_remove_all3:
  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. (* 请在此处解答 *) Admitted.

Example test_remove_all4:
  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. (* 请在此处解答 *) Admitted.

(** 完成函数 [subset] 的定义。*)
Fixpoint subset (l1 : natlist) (l2 : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. (* 请在此处解答 *) Admitted.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 有关列表的论证 *)
(**
  接下来，我们使用之前学习过的证明策略论证与列表相关的定理。
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
  因此，有关列表的很多定理，都需要(也可以)使用数学归纳法证明。
  
  假设我们需要证明命题 [P] 对任意列表 [l] 都成立。
  我们可以如下对列表 [l] 作归纳:
  - [l = []]。此时，我们需要证明 [P []] 成立。
  - [l = n :: l']。
    此时，我们需要在归纳假设 [P l'] 成立的条件下，
    证明 [P l] 成立。
*)

(** 下面使用数学归纳法证明 [app] 满足结合律。*)
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
    
  请确保你真正理解了 [induction l1 as [ | n l1' IHl1']] 的含义。
  后面，我们会看到更复杂的例子。
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
(** 请证明定理 [app_length]。*)
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

(**
  你需要通过大量的练习与思考 (练习之后的思考很重要!很重要!很重要!)
  培养证明的直觉。
  比如，分情形分析够不够用? 需不需要用数学归纳法? 对什么作归纳? 等等。
*)

(** **** 练习：3 星, standard (list_exercises) *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* 请在此处解答 *)
Admitted.

(** [app_assoc4] 有简洁的证明。不要走了弯路。*)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* 请在此处解答 *)
Admitted.

Print nonzeros. (* 你之前应该完成了 [nonzeros] 的定义。*)
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：2 星, standard (eqblist) *)
(**
  请完成 [eqblist] 的定义，它判断列表 [l1]、[l2] 是否相同。
*)

Fixpoint eqblist (l1 l2 : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. (* 请在此处解答 *) Admitted.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. (* 请在此处解答 *) Admitted.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. (* 请在此处解答 *) Admitted.

(**
  如果我们将函数 [eqblist] 看作两个列表之间的一种
   _'关系'_ (Relation), 那么它是 _自反的_ (Reflexive)。
  
  嗯，如果你现在还不明白上面那句话在说些什么，
  不要紧，直接证明下面的定理 [eqblist_refl] 就好了。 
*)
Theorem eqblist_refl : forall l : natlist,
  true = eqblist l l.
Proof.
  (* 请在此处解答 *)
Admitted.

(** **** 练习：1 星, standard (count_member_nonzero) *)
Print count. (* 你之前应该完成了 [count] 的定义。*)
Theorem count_member_nonzero : forall (l : natlist),
  1 <=? (count 1 (1 :: l)) = true.
Proof.
  (* 请在此处解答 *)
Admitted.

Print remove_one. (* 你之前应该完成了 [remove_one] 的定义。*)
(** **** 练习：3 星, advanced (remove_does_not_increase_count)  *)
Theorem remove_does_not_increase_count: forall (l : natlist),
  (count 0 (remove_one 0 l)) <=? (count 0 l) = true.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：4 星, advanced (rev_injective) *)  
(**
  请用尽可能简洁的方法证明定理 [rev_injective]: [rev] 是单射函数。
*)
Theorem rev_injective : forall (l1 l2 : natlist), 
  rev l1 = rev l2 -> l1 = l2.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* ################################################################# *)
(** * Options 可选类型 *)

Print hd.
(**
  现在，我们回到一开始对 [hd] (head) 函数的定义:
  [Definition hd (default : nat) (l : natlist) : nat]。
  为了处理 [l] 为空的情况，[hd] 要求调用者提供默认返回值 [default : nat]。
  然而，这种处理方式不够优雅:
  - 破坏了 [hd] 的语义。
  - 返回值为 [default] 时，无法区分 [l] 的表头确实为 [default] 
    与 [l] 为空的情况。
  - 给调用者增加负担。
  
  函数 [nth-bad] 是对 [hd] 的扩展，它返回列表 [l] 中的第 [n] 个元素。
  当 [l] 过短时，它返回一个任意值，这里选择返回 [42]。
  它存在与 [hd] 类似的不足。
*)

Fixpoint nth_bad (l : natlist) (n : nat) : nat :=
  match l with
  | nil => 42  (* 任意值！ *)
  | a :: l' => match n =? O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

Print option.
(**
Inductive option (A : Type) : Type :=
  | Some (x : A)
  | None. 
*)

(**
  为了解决该类问题，Coq 提供了 [option] 类型。
  [option] 类型是对 _可选值_ (Optional Value) 的一种封装。
  作为函数的返回值类型，它表示该函数可能会返回一个无意义的值，
  用以标识错误处理。
  它包含两个构造函数:
  - Some A: 表示类型为 A 的值。
  - None: 表示空值。
  
  很多程序设计语言里都有类似的 [option] 类型，
  如 Java 8 中的 [Optional]，Scala 中的 [Option]，
  Haskell 中的 [Maybe] 等。
  更多内容参见: https://en.wikipedia.org/wiki/Option_type (@wiki)。

  Coq 中的 [option] 是 _多态类型_ (Polymorphic Type)
  (下一节会介绍这个概念)。
  本节我们将被封装的值的类型限定为 [nat]。
*)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

(**
  [nth_error] 是对 [nth_bad] 的改进。
  注意，[nth_error] 的返回类型是 [natoption]:
  - 当列表 [l] 过短时，它返回 [None]，
  - 否则它将元素 [a] 封装成类型为 [natoption] 的 [Some a]，
    然后返回 [Some a]。
*)

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None (* 类型为 [natoption] *)
  | a :: l' => match n =? O with
               | true => Some a (* 类型为 [natoption] *)
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(**
  [nth_error] 中的嵌套模式匹配 [match n=? O]
  也可以换成条件表达式，
  如下面的 [nth_error_if] 所示。
*)

Fixpoint nth_error_if (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => 
      if n =? O then Some a (* 替换 [nth_error] 中的模式匹配 *)
                else nth_error_if l' (pred n)
  end.

(**
  接收到类型为 [natoption] 的值 [v] 以后，
  我们通常会对其进行模式匹配 [match v with]:
  - 如果为 [None]，则做特殊处理。
  - 如果为 [Some a]，则对 [a] 做处理。
*)

(** **** 练习：2 星, standard (hd_error) *)
(** 请使用 [natoption] 思想修改之前定义的 [hd] 函数。*)

Definition hd_error (l : natlist) : natoption
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_hd_error1 : hd_error [] = None.
Proof. (* 请在此处解答 *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. (* 请在此处解答 *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)
End NatList.

(* ################################################################# *)
(** * Trees: 基础数据类型 *)

(**
  我们以 _'二叉树'_ (Binary Tree) 为例。
  二叉树在计算机科学中占有重要地位，应用之一就是 (平衡) 二叉搜索树。
  
  顾名思义，在二叉树中，每个节点 (Node) 最多有两个子节点 (Children)，
  分别称为左子节点 (Left Child) 与右子节点 (Right Child)。
  在本节，我们仍然限制每个节点中的元素都是自然数类型。
  
  我们使用归纳方式定义(自然数)二叉树 nat_bin_tree。
  (注意，我们将二叉树缩写成 bin_tree，而不是 btree。
  这是因为，BTree 是计算机科学中的另一个专有名词。)
  
  二叉树有且仅有两种构造方式:
  - 空树 [Empty] 是二叉树。
  - 如果 [L] 是二叉树，[R] 是二叉树，[n] 是自然数，则 [Node L n R]
    是二叉树。
    [L] 称为 [Node L n R] 的左子树，[R] 称为 [Node L n R] 的右子树。
    [Node L n R] 称为 [L] 与 [R] 的 _'父节点'_ (Parent)。
    左右子树都为 [Empty] 的节点称为 _'叶节点'_ (Leaf)。
    没有父节点的节点称为 _'根节点'_ (Root)。
*)

Inductive nat_bin_tree : Type :=
  | Empty
  | Node (L : nat_bin_tree) (n : nat) (R : nat_bin_tree).

(** 在执行下面的命令之前，先想一想它的结果。 *)
Check Empty.
Check Node.
Check (Node (Empty) 5 (Empty)).

(** **** 练习：2 星, standard (functions on [nat_bin_tree]) *)
(** 下面你需要为 [nat_bin_tree] 定义一些函数，并编写测试用例。*)

(**
  函数 [nsize] 计算二叉树 [t] 的大小，即 [t] 中节点的数目。
  注意，空树 [Empty] 的大小为 0。
*)
Fixpoint nsize (t : nat_bin_tree) : nat 
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

(**
  函数 [nsum] 计算二叉树 [t] 所有节点中的元素之和。
*)
Fixpoint nsum (t : nat_bin_tree) : nat 
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

(**
  函数 [nreflect] 交换 _每个_节点的左右子树。
*)
Fixpoint nreflect (t : nat_bin_tree) : nat_bin_tree
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

(**
  与 [natlist] 一样，[nat_bin_tree] 也是归纳定义的，
  我们也可以对 [nat_bin_tree] 使用数学归纳法。
  
  不同的是，[nat_bin_tree] 的 [Node] 构造函数中
  含有_两个_ [Node] 类型的参数。
  因此，对 [nat_bin_tree] 类型的 [t] 做数学归纳时，
  在归纳步骤，我们有两个归纳假设，分别针对 [t] 的左右子树。
  
  比如，下面证明开头 [induction t as [ | L IHL n R IHR]]
  中的 [IHL] 与 [IHR] 分别表示针对左子树 [L] 与右子树 [R]
  的归纳假设。
  
  了解了这些，你应该可以完成下面的证明了。
*)
Theorem nreflect_involutive: forall t : nat_bin_tree,
  nreflect (nreflect t) = t.
Proof.
  induction t as [ | L IHL n R IHR].
  (* t = Empty *)
  (* t = Node L n R *)
Admitted.

(**
  函数 [height] 计算二叉树 [t] 的高度:
  - [Empty] 的高度记为 -1。
  - 节点 [Node L n R] 的高度是它的两个子树的最大高度加 1。
  - 树 [t] 的高度是它的根结点的高度。
  
  你可以使用 [Nat.max] 函数，或者自定义求最大值的函数。
*)
Fixpoint height (t : nat_bin_tree) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

(** 请证明定理 [nreflect_preserve_height]: [nreflect] 不改变树的高度。*)
Theorem nreflect_preserve_height : forall t : nat_bin_tree,
  height (nreflect t) = height t.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* Fri Jul 19 00:32:19 UTC 2019 *)