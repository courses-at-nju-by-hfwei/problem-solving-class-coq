(** * FP: 函数式程序设计——高阶函数 *)

(** 
  本节依赖于 [Poly.v] (你需要先阅读它)。
  你需要先编译 [Poly.v] 得到 [Poly.vo]。
  编译方法：在 CoqIDE 中打开 [Poly.v]，
  执行 "Compile" 菜单中的 "Compile Buffer" 命令。
*)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.

(* ################################################################# *)
(** * 高阶函数 *)

(**
  本节，我们要正式进入函数式程序设计的世界。
  
  说起函数式程序设计，就不得不提起与它紧密相关的一系列概念:
  不可变性 (Immutable)、纯函数 (Pure Functions)、
  单子 (Monad)、持久性数据结构 (Persistent Data Structures)、
  高阶函数 (High-Order Functions)、柯里化 (Currying)、
  惰性求值 (Lazy Evaluation)、类型系统 (Type Systems)、
  引用透明性 (Referential Transparency) 等等。
  
  要想真正掌握函数式程序设计，就需要深入了解这些概念。
  其中一些概念至今仍是程序设计语言 (Programming Language; PL) 
  领域的研究课题。
  如果你学完本节之后，对函数式程序设计产生了兴趣，
  甚至于对程序设计语言理论本身产生了兴趣，
  那么本节的目的就达到了。
   
  我们不可能面面俱到地介绍上面的概念。
  本节重点介绍 _'高阶函数'_ 的含义与应用。
  它是函数式程序设计最典型的特征。
    
  所谓高阶函数，就是可以操作其它函数的函数。
  具体来说，高阶函数
  - 的参数可以是函数
  - 的返回值也可以是函数
  
  注意，高阶函数的参数或返回值仍然可能是个高阶函数。
  
  其实，你已经在数学中接触过高阶函数的概念了。
  比如求导/积分操作(视为函数)，它接受一个函数，返回另一个函数。
  
  我们先看一个简单的例子:
*)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

(**
  函数 [doit3times] 的参数 [f : X -> X] 本身是个从 [X] 到 [X] 的函数。
  它连续将 [f] 作用在另一个参数 [n : X] 上三次。
*)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(**
  我们现在知道了，在高阶函数中，函数可以作为参数，也可以作为返回值。
  而作为参数、作为返回值是"数据"的基本"权利"。
  所以，在函数式程序设计中，一种常见的说法是:
  函数也是一等公民 (First-Class Citizens)。
  
  作为一等公民，我们还会看到，你可以像存储、组织数据一样存储、组织函数，
  比如把若干函数放在一个列表里。(TODO: @hengxin 例子???)
  
  在函数式程序设计的长期实践中，
  人们已经总结出了多种经常会用到的功能简单而强大的高阶函数，
  比如 filter, map, fold, zip 等。
  这里的每一个高阶函数都是对一类常见"行为"的抽象。
  "行为"是可以组合的，通过组合这些高阶函数，我们经常能得到一种优雅的解决方案。
  
  下面我们就来介绍这些高阶函数。
  Just Enjoy It!
*)

(* ================================================================= *)
(** ** Filter (过滤器) *)

(** 
  高阶函数 [filter] 接受一个元素类型为 [X] 的列表
  和一个从 [X] 到 [bool] 的函数 (值域为 [bool] 的函数也称为谓词),
  返回另一个元素类型也为 [X] 的列表，这个结果列表中仅包含满足谓词的元素。
  
  一言以蔽之，[filter] "过滤出" 了满足 [test] 条件的元素。
*)

Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(**
  比如，[filter evenb [1;2;3;4]] 返回的列表中仅包含原列表中的偶数，
  即 [2;4]。
*)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

(**
  在 [test_filter2] 中，我们要从一组列表过滤出长度为1的列表。
  为此，我们需要先定义谓词 [length_is_1]。
*)
Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
  filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
    = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 匿名函数 *)

(** 
  在上面的例子中，我们需要先定义一个名为 [length_is_1] 的函数 (谓词)。
  但是，[length_is_1] 并没有任何通用性，为了它单独定义一个函数，
  实在是划不来。
  
  不必沮丧。
  这正是 _'匿名函数'_ () 的用武之地。
*)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(**
  表达式 [(fun n => n * n)] 表示一个函数。
  - [fun] 是关键词, 表示要定义一个函数。
  - [n] 是这个函数的参数。
  - [=>] 用于区分函数头与函数体。
  - [n * n] 是函数体。
  
  这里的重点是, 上面的函数没有名字，没有名字，没有名字。
  既然我们不打算在以后使用它，为什么要费神给它取个名字呢?
*)

(** 我们可以使用匿名函数重写 [test_filter2]。*)
Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
      = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(** **** 练习：2 星, standard (filter_even_gt7)  

  请使用 [filter] 完成函数 [filter_even_gt7] 的定义,
  它接受一个自然数列表，过滤出其中大于 [7] 的偶数。
*)

Definition filter_even_gt7 (l : list nat) : list nat
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. (* 请在此处解答 *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (partition)  

  请使用 [filter] 完成函数 [partition]:

  partition : forall X : Type,
    (X -> bool) -> list X -> list X * list X

  给定元素类型为 [X] 的列表 [l : list X],
  [test] 谓词 [test : X -> bool],
  [partition] 返回一个列表序对 [list X * list X],
  其中, 序对中的第一个列表仅包含原列表 [l] 中满足谓词 [test] 的元素,
  而序对中的第二个列表则包含原列表 [l] 中不满足谓词 [test] 的元素。
  需要注意的是, 两个列表中元素的顺序应当与它们在原列表中的顺序相同。
*)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_partition1:
  partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. (* 请在此处解答 *) Admitted.

Example test_partition2:
  partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Map (映射) *)

(** 
  高阶函数 [map] 接受一个元素类型为 [X] 的列表 [l : list X]
  与一个从 [X] 到 [Y] 的函数 [f : X -> Y],
  返回一个元素类型为 [Y] 的列表。
  
  一言以蔽之, [map] 将原列表中的每个类型为 [X] 的元素映射为类型为 [Y] 的元素。
  啰嗦一点, 假设原列表是 [l = [n1; n2; n3; ...]],
  则返回的列表为 [[f n1; f n2; f n3; ...]]。
*)

Fixpoint map {X Y: Type} (f : X -> Y) (l : list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** 在 [test_map1] 中，[map] 的作用是对原列表中的每个元素加 3。*)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

(** 
  在 [test_map2] 中，[map] 的作用是判断原列表中的每个元素是否为奇数，
  返回判断结果 (false 或 true) 构成的列表。
*)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

(**
  [map] 可以做什么样的转换取决于你传给它什么样的函数。
 (取决于你的想象力)
*)

Example test_map3:
  map (fun n => [evenb n; oddb n]) [2; 1; 2; 5]
    = [[true; false]; [false; true]; [true; false]; [false; true]].
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** 习题 *)

(** **** 练习：3 星, standard (map_rev)
  请证明 [map] 和 [rev] 可交换。你可能需要先证明一个引理。
*)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：2 星, standard, recommended (flat_map)  

  [map] 通过一个类型为 [X -> Y] 的函数将 [list X] 转化为 [list Y]。
  
  下面要定义的函数 [flat_map]则通过一个类型为 [X -> list Y]的函数
  先将 [X] 的每个元素转化为一个列表 [list Y]，
  然后将这些 [list Y] 列表 "压扁" (flatten) 为一个类型为 [list Y] 的列表。
  例如:

        flat_map (fun n => [n; n+1; n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
      
  请给出 [flat_map] 的定义。
*)

Fixpoint flat_map {X Y: Type} (f : X -> list Y) (l : list X)
                  : (list Y)
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example test_flat_map1:
  flat_map (fun n => [n; n; n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(**
  我们还可以使用 [map] 对 [option] 所封装的数据进行转化，如下定义 [option_map]。
*)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* ================================================================= *)
(** ** Fold (折叠) *)

(**
  在函数式程序设计中，一个更为强大的 (Powerful; 请思考，如何定义函数的 Power?) 
  高阶函数是 [fold]。它可以将一个列表 "折叠" 成一个值。
  
  如下定义的 [fold] 接受
  - 一个类型为 [X -> Y -> Y] 的函数 [f];
  - 一个类型为 [list X] 的列表 [l]; 
  - 一个类型为 [Y] 的值 [b]。
  
  它们的含义如下:
  - [f] 是 "折叠" 时使用的计算方法;
    [f] 可看作接受类型分别为 [X] 与 [Y] 的两个参数的函数，
    它返回类型为 [Y] 的值。
  - [l] 是 "被折叠" 的列表;
  - [b] 是默认初始值。
  
  [fold] 返回类型为 [Y] 的值。注意，该类型与 [f] 的返回类型相同。
  
  [fold] 的 "折叠" 过程如下:
  - 如果 [l = nil]，则直接返回默认初始值;
  - 如果 [l = h :: t]，则先递归折叠表尾 [t]，
    得到类型为 [Y] 的值 [fold f t b]，然后利用 [f] 将它与表头进行折叠，
    得到类型为 [Y] 的值 [f h (fold f t b)]。 
*)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check @fold.
(* ===> forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y *)

(** 
  直观地讲，[fold] 的效果等同于将二元运算符 [f] 插入到给定列表 [l]
  的每一对相邻元素之间。
  例如，[fold plus [1; 2; 3; 4] 0] 
  的效果等同于 [1 + (2 + (3 + (4 + 0)))].
  
  注意, [fold h (fold f t b)] 在计算时先递归处理表尾 [t]，
  因此，[fold] 会以 "从右向左" 的顺序折叠列表
  (对应于 [1 + (2 + (3 + (4 + 0)))] 中的 "加法右结合")。
*)

Check plus.
Example fold_example0 : fold plus [1; 2; 3; 4] 0 = 10.
Proof. reflexivity. Qed.

Check mult.
Example fold_example1 :
  fold mult [1; 2; 3; 4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true; true; false; true] true = false.
Proof. reflexivity. Qed.

Check @app.
Example fold_example3 :
  fold app [[1]; []; [2;3]; [4]] [] = [1; 2; 3; 4].
Proof. reflexivity. Qed.

(**
  需要注意的是，[fold] 接受的函数 [f] 的类型为 [X -> Y -> Y]，
  它并不要求 [X] 与 [Y] 是相同的类型。
  这就为 [fold] 所能做的事情提供了很多可能性。
  
  TODO: @ant-hengxin 例子。
*)

(**
  下面，我们通过练习见识一下 [fold] 的强大之处:
  我们使用 [fold] 实现之前定义过的一些列表函数。
*)

(** **** 练习：2 星, standard (fold_length) *)

(** 
  [fold_length] 使用 [fold] 实现了 [length]。
  请证明 [fold_length] 的正确性 (定理 [fold_length_correct])。
  (提示: 必要时使用 [reflexivity] 而不是 [simpl]。)   
*)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
(* 请在此处解答 *)
Admitted.

(** **** 练习：3 星, standard (fold_map) *)  
(** 请用 [fold] 定义 [map]，并证明其正确性。*)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) 
              : list Y
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Theorem fold_map_correct : 
  forall (X Y : Type) (f : X -> Y) (l : list X),
    fold_map f l = map f l.
Proof.
(* 请在此处解答 *)
Admitted.

(** **** 练习：3 星, standard (fold_filter) *)  
(** 请用 [fold] 定义 [filter]，并证明其正确性。*)

Definition fold_filter {X : Type} (test : X -> bool) (l : list X)
                : (list X)
(* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Theorem fold_filter_correct : 
  forall (X : Type) (test : X -> bool) (l : list X),
    fold_filter test l = filter test l.
Proof.
(* 请在此处解答 *)
Admitted.

(* ================================================================= *)
(** ** Zip () *)
  
  (** TODO: @hengxin *)
  
(* ================================================================= *)
(** ** 一个函数可以作为另一个函数的返回值 *)

(**
  在 Coq 中 (更一般地，在函数式程序设计语言中)，
  [->] 操作符是右结合的。
  因此，函数 [f : A -> B -> C] 的类型其实是 [A -> (B -> C)]。
  (注意，在逻辑中，蕴含联结符 [->] 也是右结合的。这并非巧合。)
  
  为什么要强调 [->] 的右结合性呢?
  之前，我们在介绍 [f : A -> B -> C] 时，
  说它是接受两个参数，返回一个参数的函数。
  更形式化地讲，我们认为 [f] 的类型是 [f : (A * B) -> C]。 
  这没有错，因为在命令式程序设计语言 (如 C 语言) 中，
  我们已经习惯了一次性为 [f] 传入它所能接受的两个参数。
  
  但是，在函数式程序设计语言里，你可以将 [f] 仅作用在一个参数上 [a : A]。
  那 [f a] 的结果是什么呢?
  
  我们前面提到 [f : A -> B -> C] 的类型是 [A -> (B -> C)]，
  也就是说，[f] 的类型其实是: 接受类型为 [A] 的一个参数，
  返回类型为 [B -> C] 的函数。
  
  因此，[f a] 的返回值是一个类型为 [B -> C] 的函数。
  既然返回结果是个函数，我们可以继续将这个函数应用到类型为 [b : B] 的值上:
  [f a b] 返回类型为 [C] 的值。
  
  总结一下，在函数式程序设计语言中，我们可以 "部分" (Partial) 应用
  某个函数。此时，我们得到的返回值仍然是个函数。
  
  这种将类型 [f : (A * B) -> C] 视作 [f : A -> (B -> C)] 的方式
  被称为 "柯里化" (Currying)。
  Curry 指的是逻辑学家 Haskell Curry 
  (没错，Haskell 语言也是以他的名字命名的)。

  
  反之，我们也可以将 [A -> B -> C] 解释为 [(A * B) -> C]。
  这被称作 "反柯里化" (Uncurrying)。
    
  更多相关理论知识，可以参考 
  [Currying @ wiki](https://en.wikipedia.org/wiki/Currying)。
*)

(** 我们来看一些具体的例子。*)
Check plus.
(* ==> nat -> nat -> nat *)

(**
  当我们部分应用 [plus] 到一个自然数上时，我们就得到另一个函数。
  例如，[plus 3] 返回一个函数 [nat -> nat]，
  它的作用就是把任何传入的值加三。 
*)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.

Check @doit3times.
(* @doit3times : forall X : Type, (X -> X) -> X -> X *)

(**
  回忆: [doit3times] 将接受的函数作用三次。
  我们可以将 [plus3] 传给 [doit3times]。
*)
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * 选做练习 *)

(** 高能预警: 该练习难度较大。它要求你能熟练运用高阶函数。*)

(**
  在该练习中，我们使用函数定义自然数。
  自然数 [n] 表示把某个函数 [f] 作用 [n] 次。
  这种表示方法称为 Church Numerals。
  Church 指的是数学家 Alonzo Church。
*)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(** 自然数 [one] 表示将 [f] 作用在参数 [x] 上一次 [f x]。*)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** 自然数 [two] 表示将 [f] 作用在参数 [x] 上两次 [f (f x)]。*)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** 如何定义自然数 [zero] 呢? 答案很简单: 把参数原样返回就好了。*)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** **** 练习：1 星, advanced (church_succ)  *)

(** 先热热身: 请定义自然数上的后继函数 [succ]。*)

Definition succ (n : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *).
Admitted.

Example succ_1 : succ zero = one.
Proof. (* 请在此处解答 *) Admitted.

Example succ_2 : succ one = two.
Proof. (* 请在此处解答 *) Admitted.

(** **** 练习：2 星, advanced (church_plus) *)

(** 加大难度: 请定义自然数上的加法运算 [plus]。*)
Definition plus (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* 请在此处解答 *) Admitted.

Example plus_1_1_1 :
  plus (plus one one) one = plus one (plus one one).
Proof. (* 请在此处解答 *) Admitted.

(** **** 练习：3 星, advanced (church_mult)  *)

(** 难度升级: 请定义自然数上的乘法运算 [mult]。*)

Definition mult (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* 请在此处解答 *) Admitted.

Example mult_2 : mult zero (plus one one) = zero.
Proof. (* 请在此处解答 *) Admitted.

Example mult_3 : mult two two = plus two two.
Proof. (* 请在此处解答 *) Admitted.

(** **** 练习：4 星, advanced (church_exp)  *)

(** 难度再度升级: 请定义自然数上的幂运算 [exp]。 *)

Definition exp (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example exp_0 : exp two zero = one.
Proof. (* 请在此处解答 *) Admitted.

Example exp_1 : exp two one = two.
Proof. (* 请在此处解答 *) Admitted.

Example exp_2 : exp two two = plus two two.
Proof. (* 请在此处解答 *) Admitted.

Definition three := @doit3times.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* 请在此处解答 *) Admitted.

(** [] *)

End Church.