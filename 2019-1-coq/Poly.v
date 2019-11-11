(** * Poly: 多态 *)

(** 
  本节依赖于 [Lists.v] (你需要先阅读它)。
  你需要先编译 [Lists.v] 得到 [Lists.vo]。
  编译方法：在 CoqIDE 中打开 [Lists.v]，
  执行 "Compile" 菜单中的 "Compile Buffer" 命令。
*)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

(**
  在介绍函数式程序设计之前，我们需要先介绍另外一个概念: _多态_ (Polymorphic)。
  它与程序设计语言的类型系统有关。
*)
    
(* ################################################################# *)
(** * 多态 *)

(* ================================================================= *)
(** ** 多态列表 *)

(** 
  在 [Lists.v] 中，我们定义了自然数列表 [natlist] 与作用于其上的函数。
  依葫芦画瓢，我们还可以定义字符列表 (即，字符串)、布尔值列表、日期列表、
  甚至自然数列表的列表，并且分别为它们定义一系列与列表相关的操作函数。
  
  但是，作为程序员，你根本无法忍受把同样的事情做三遍，
  根本无法忍受把同样的事情做三遍，根本无法忍受把同样的事情做三遍。
  
  稍加思考，就会发现，这些定义大同小异，不同的仅是列表中元素的类型而已。
  因此，我们可以考虑把类型抽象出来，作为一个参数。
  于是就有了“多态”机制，它允许程序员定义一个可以适用于任意类型的类型或函数。
  
  比如，下面的 [list] 所定义的列表中的元素可以是任意类型 (用 X 表示)。
*)

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** 
  与 [Lists.v] 中 [natlist] 的定义相比，[list] 有两处变化:
  - 在定义的头部多了 [(X : Type)]。
    [X] 称为类型参数。
    在使用 [list] 时，我们可以把 [X] 替换成任何具体的类型。
    比如，[list nat] 表示自然数列表，[list bool] 表示布尔值列表，等等。
  - 在构造函数 [cons] 中，我们使用 [x : X] 代替了 [natlist] 中
    具体的 [n : nat]，并用 [(l : list X)] 代替了 [natlist]。
*)

(**
  [list] 的类型是什么呢?
  上面我们提到，[X] 是_类型_参数，
  而 [list X] 表示元素类型为 [X] 的列表_类型_。
  因此，我们可以将 [list] 看作一个函数，它接受一个类型 (X : Type)，
  返回另一个类型 [list X]。
*)

Check list.
(* ===> list : Type -> Type *)

(** 
  构造函数 [nil] 的类型是什么呢?
  你可以通过运行下面的 [Check nil] 来查看。
  目前你不必完全理解它的含义，只要能意会即可:
  对于任意类型 [X]，返回 [List X]。
*)

Check nil.
(* ===> nil : forall X : Type, list X *)

(** 
  类似地，你可以查看 [cons] 的类型:
  对于任意的类型 [X]，给定类型为 [X] 的元素与列表 [list X]，
  返回另一个列表 [list X]。
*)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** 
  定义 [list] 中的类型参数 [X] 自动成为构造函数 [nil] 与 [cons] 的类型参数。
  也就是说，[nil] 与 [cons] 是多态构造函数。
  在使用它们时，我们需要提供 [X] 对应的具体类型。
  一个基本的使用规则是，[nil] 与 [cons] 不能独立出现，
  它们的后面一定要跟着一个具体的类型。
*)

Check (nil nat).
(* ===> nil nat : list nat *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

Check (cons nat 2 (cons nat 1 (nil nat))).
(* ===> cons nat 2 (cons nat 1 (nil nat)) : list nat *)

(* ----------------------------------------------------------------- *)
(** *** 隐式参数 *)

(** 
  作为程序员，在 [cons] 或 [nil] 之后总是要写个 [X] (如 [nat])
  是不可忍受的。
  当我写 [cons nat 3 (nil nat)] 时，难道 Coq 就不能聪明一点，
  根据这里的 [3] 推断出我是在构造一个 [list nat] 类型的列表吗?
  
  当然可以。这就是 Coq 的 _类型推断_ (Type Inference) 系统。
  你只需要用 [Arguments] 指令"授权" Coq 可以自行推断就可以了。
  
  [Arguments] 后跟构造函数的名字以及它的参数名，
  其中放在花括号的参数称为 _隐式参数_ (Implicit Arguments)。
  当你在后面使用构造函数的时候，就可以不用显式地写明这些隐式参数了，
  Coq 会自行推断出来。
  
  TODO: (@ant-hengxin) 通配符在 [Arguments] 中的使用。  
*)

Arguments nil {X}.
Arguments cons {X} x l.

(** 现在我们不必再提供繁琐的类型参数了。*)

Check (cons 1 (cons 2 (cons 3 nil))).

(**
  [Arguments] 机制同样适用于普通函数 (即，不限于构造函数)。
  比如, [Arguments repeat {X} x count.] 告诉 Coq 在函数 [repeat]
  中，[X] 是隐式参数。
  不过，对于普通函数，我们通常使用另一种更简洁的写法:
  在定义多态函数时，我们将类型参数 [X : Type] 放在花括号里即可。
  
  下面的 [repeat] 是 [Lists.v] 中 [repeat] 的多态版本。
  请仔细阅读该函数的定义，确保你理解其中的每一部分。
*)

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.

Example test_repeat1 :
  repeat 4 2 = cons 4 (cons 4 nil).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat false 1 = cons false nil.
Proof. reflexivity. Qed.

(**
  注意: 在上面的两个例子中，我们不需要写成 [repeat nat 4 2] 
  或 [repeat bool false 1]。
  Coq 可以推断出 [nat] 与 [bool] 类型。
  
  实际上，在声明了隐式参数的情况下，
  写 [repeat nat 4 2] 或 [repeat bool false 1] 是错误的
  (你不妨试一试，查看并理解 CoqIDE 右下方 [Messages] 窗口的错误信息)。
*)

(** 
  隐式参数配合类型推断为我们省去很多繁琐的工作。
  不过，有些时候信息不足，导致 Coq 无法推断类型。
*)

Fail Definition mynil := nil. (* [Fail] 确保该指令会失败。*)

(**
  显然，Coq 无法单凭一个 [nil] 推断出列表中的元素类型。
  这种情况下，我们需要显式地提供具体类型，比如下面的 [: list nat]。
*)

Definition mynil : list nat := nil.

(** 我们还可以在函数名前加上前缀 [@] 来强制将隐式参数变成显式的。*)

Check @nil.
(** ===> @nil: forall X : Type, list X *)

Definition mynil' := @nil nat.

(** 与 [Check nil] 比较: *)
Check nil.
(** ===> nil : list ?X where ?X : [ |- Type]) 不理解? 没关系。*)

Check @cons.
(** ===> @cons : forall X : Type, X -> list X -> list X *)
Check @repeat.
(** ===> @repeat : forall X : Type, X -> nat -> list X *)

(**
  借助于 Coq 强大的类型推断系统，我们还可以更激进一些:
  省掉所有参数的类型标注。
  不过，我们并不推荐这么做，因为这会降低代码的可读性。
*)

Fixpoint repeat' {X} x count : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat' x count')
  end.

Check @repeat'. (* 返回结果与 [Check @repeat] 相同。*)
(** ===> forall X : Type, X -> nat -> list X *)

(* ----------------------------------------------------------------- *)
(** 下面给出多态列表的一些标准多态函数的定义。*)

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
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
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(** 隐式参数与类型推断也适用于 [Notation]。*)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(** *** 练习 *)

(** **** 练习：2 星, standard (poly_exercises) *)
(** 
  在我们享受多态带来的便捷的时候，我们并不需要为多态单独发展出一套证明理论。
  请完成下面的证明，体会这一点 (你之前在 [Lists.v] 中所做的证明在这里同样适用)。 
*)

Theorem app_nil_r : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* 请在此处解答 *)
Admitted.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 请在此处解答 *)
Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* ================================================================= *)
(** ** 多态序对 *)

(** 
  类似地，我们可以定义自然数序对 [natprod] 的多态版本:
  _'多态序对'_ (Polymorphic Pairs)，也称为 _'积'_ (Products)'。
*)

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

(** 
  我们可以使用 [Notation] 定义标准的 _'积类型'_ (Product Types)。
  Product Types 是类型理论中的概念，类似的还有 Sum Types。
  听上去有些唬人，其实概念上很简单:
  就是将两种类型组成在一起，构成一个复合类型。
  类似于 C 语言中的 'Struct' (仅含两个域)。
  从逻辑的角度讲，它对应于逻辑联结词 "and"。
  
  现在，你猜一下，Sum Types 是什么含义?
  它类似于 C 语言中的什么类型? 对应于哪个逻辑联结词?
  
  参考资料: https://en.wikipedia.org/wiki/Product_type 。
*)

Notation "X * Y" := (prod X Y) : type_scope.

(**
  标注 [: type_scope] 告诉 Coq 记法 [X * Y] 只在解析"类型"时使用，
  从而避免与乘法符号冲突。
*)

(** 
  注意: 不过要记住 [(x,y)] 是一个值, [X * Y] 是一个类型。
  如果 [x] 的类型为 [X], [y] 的类型为 [Y],
  那么 [(x,y)] 的类型就是 [X * Y]。
*)

(** 下面是 [fst] 与 [snd] 的多态版本。*)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** 
  函数 [combine] 将两个列表 [lx : list X] 与 [ly : list Y]
  合并成一个序对 [list (X * Y)] 的列表。
  该函数通常被称为 [zip]。
*)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** [combine] 的类型是什么? *)
Check @combine.

Compute (combine [1; 2] [false; false; true; true]).

(** **** 练习：2 星, standard, recommended (split)  

  函数 [split] 是 [combine] 的右逆 (right inverse),
  即满足 combine (fst (split l)) (snd (split l)) = l。
  该函数通常被称为 [unzip]。

  请完成 [split] 的定义，确保它能够通过给定的单元测试。
*)

Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y)
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_split:
  split [(1,false); (2,false)] = ([1; 2], [false; false]).
Proof.
  (* 请在此处解答 *)
Admitted.

(** TODO: (@ant-hengxin) Prove it first. *)
Theorem combine_split: forall (X Y : Type) (l : list (X * Y)),
  combine (fst (split l)) (snd (split l)) = l.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(* ================================================================= *)
(** ** 多态可选类型 *)

(** 
  [option] 是 [lists.v] 中定义的可选类型 [natoption] 的多态版本。
*)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(** 下面的 [nth_error] 是多态函数了。 *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
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

(** **** 练习：1 星, standard, optional (hd_error_poly)  
  请完成 [Lists.v] 中 [hd_error] 的多态版本，确保它能通过下面的单元测试。
*)

Definition hd_error {X : Type} (l : list X) : option X
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* 请在此处解答 *) Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* 请在此处解答 *) Admitted.
(** [] *)

(* Fri Jul 19 00:32:20 UTC 2019 *)