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
(** * 函数作为数据 *)

(** 和其它现代编程语言，包括所有函数式语言（ML、Haskell、
    Scheme、Scala、Clojure 等）一样，Coq 也将函数视作“一等公民（First-Class Citizens）”，
    即允许将它们作为参数传入其它函数、作为结果返回、以及存储在数据结构中等等。 *)

(* ================================================================= *)
(** ** 高阶函数 *)

(** 用于操作其它函数的函数通常叫做_'高阶函数'_。以下是简单的示例： *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** 这里的参数 [f] 本身也是个（从 [X] 到 [X] 的）函数，
    [doit3times] 的函数体将 [f] 对某个值 [n] 应用三次。 *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

(**
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.
*)

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** 过滤器 *)

(** 下面是个更有用的高阶函数，它接受一个元素类型为 [X] 的列表和一个
    [X] 的谓词（即一个从 [X] 到 [bool] 的函数），然后“过滤”此列表并返回一个新列表，
    其中仅包含对该谓词返回 [true] 的元素。 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** 例如，如果我们将 [filter] 应用到谓词 [evenb] 和一个数值列表 [l]
    上，那么它就会返回一个只包含 [l] 中偶数的列表。 *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** 我们可以使用 [filter] 给出 [Lists] 中 [countoddmembers]
    函数的简洁的版本。 *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** 匿名函数 *)

(** 在上面这个例子中，我们不得不定义一个名为 [length_is_1] 的函数，
    以便让它能够作为参数传入到 [filter] 中，由于该函数可能再也用不到了，
    这有点令人沮丧。我们经常需要传入“一次性”的函数作为参数，之后不会再用，
    而为每个函数取名是十分无聊的。

    幸运的是，有一种更好的方法。我们可以按需随时构造函数而不必在顶层中声明它
    或给它取名。 *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** 表达式 [(fun n => n * n)] 可读作“一个给定 [n] 并返回 [n * n] 的函数。” *)

(** 以下为使用匿名函数重写的 [filter] 示例：*)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** 练习：2 星, standard (filter_even_gt7)  

    使用 [filter]（而非 [Fixpoint]）来编写 Coq 函数 [filter_even_gt7]，
    它接受一个自然数列表作为输入，返回一个只包含大于 [7] 的偶数的列表。 *)

Definition filter_even_gt7 (l : list nat) : list nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* 请在此处解答 *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (partition)  

    使用 [filter] 编写一个 Coq 函数 [partition]：

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   给定一个集合 [X]、一个类型为 [X -> bool] 的测试函数和一个 [list X]，
   [partition] 应当返回一个列表的序对。该序对的第一个成员为包含原始列表中
   满足该测试的子列表，而第二个成员为包含不满足该测试的元素的子列表。
   两个子列表中元素的顺序应当与它们在原始列表中的顺序相同。 *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* 请在此处解答 *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 映射 *)

(** 另一个方便的高阶函数叫做 [map]。 *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** 它接受一个函数 [f] 和一个列表 [ l = [n1, n2, n3, ...] ]
    并返回列表 [ [f n1, f n2, f n3,...] ]，其中 [f] 可分别应用于 [l]
    中的每一个元素。例如： *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** 输入列表和输出列表的元素类型不必相同，因为 [map] 会接受_'两个'_类型参数
    [X] 和 [Y]，因此它可以应用到一个数值的列表和一个从数值到布尔值的函数，
    并产生一个布尔值列表： *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** 它甚至可以应用到一个数值的列表和一个从数值到布尔值列表的函数，
    并产生一个布尔值的_'列表的列表'_： *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** 习题 *)

(** **** 练习：3 星, standard (map_rev)  

    请证明 [map] 和 [rev] 可交换。你可能需要定义一个辅助引理 *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, recommended (flat_map)  

    函数 [map] 通过一个类型为 [X -> Y] 的函数将 [list X] 映射到 [list Y]。
    我们可以定义一个类似的函数 [flat_map]，它通过一个类型为 [X -> list Y]
    的函数 [f] 将 [list X] 映射到 [list Y]。你的定义应当可以“压扁”[f]
    的结果，就像这样：

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* 请在此处解答 *) Admitted.
(** [] *)

(** Lists are not the only inductive type for which [map] makes sense.
    Here is a [map] for the [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** 练习：2 星, standard, optional (implicit_args)  

    [filter] 和 [map] 的定义和应用在很多地方使用了隐式参数。
    请将隐式参数外层的花括号替换为圆括号，然后在必要的地方补充显式类型形参并用
    Coq 检查你做的是否正确。（本练习并不会打分，你可以在本文件的_'副本'_中做它，
    之后丢掉即可。）

    [] *)

(* ================================================================= *)
(** ** 折叠 *)

(** 一个更加强大的高阶函数叫做 [fold]。本函数启发自“[reduce] 归约”
    操作，它是 Google 的 map/reduce 分布式编程框架的核心。 *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** 直观上来说，[fold] 操作的行为就是将给定的二元操作符 [f]
    插入到给定列表的每一对元素之间。例如，[ fold plus [1;2;3;4] ]
    直观上的意思是 [1+2+3+4]。为了让它更精确，我们还需要一个“起始元素”
    作为 [f] 初始的第二个输入。因此，例如

       fold plus [1;2;3;4] 0

    就会产生

       1 + (2 + (3 + (4 + 0))).

    以下是更多例子： *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(** **** 练习：1 星, advanced (fold_types_different)  

    我们观察到 [fold] 由 [X] 和 [Y] 这_'两个'_类型变量参数化，形参 [f]
    则是个接受 [X] 和 [Y] 并返回 [Y] 的二元操作符。你能想出一种 [X] 和
    [Y] 不同时的应用情景吗？ *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_fold_types_different : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 用函数构造函数 *)

(** 目前我们讨论过的大部分高阶函数都是接受函数作为参数的。
    现在我们来看一些将函数作为其它函数的结果_'返回'_的例子。
    首先，下面是一个接受值 [x]（由某个类型 [X] 刻画）并返回一个从
    [nat] 到 [X] 的函数，当它被调用时总是产生 [x] 并忽略其 [nat] 参数。 *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** 实际上，我们已经见过的多参函数也是讲函数作为数据传入的例子。
    为了理解为什么，请回想 [plus] 的类型。 *)

Check plus.
(* ==> nat -> nat -> nat *)

(** 该表达式中的每个 [->] 实际上都是一个类型上的_'二元'_操作符。
    该操作符是_'右结合'_的，因此 [plus] 的类型其实是 [nat -> (nat -> nat)]
    的简写，即，它可以读作“[plus] 是一个单参数函数，它接受一个 [nat]
    并返回另一个函数，该函数接受另一个 [nat] 并返回一个 [nat]”。
    在上面的例子中，我们总是将 [plus] 一次同时应用到两个参数上。
    不过如果我们喜欢，也可以一次只提供一个参数，这叫做_'偏应用（Partial
    Application）'_。 *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ################################################################# *)
(** * 附加练习 *)

Module Exercises.

(** **** 练习：2 星, standard (fold_length)  

    列表的很多通用函数都可以通过 [fold] 来实现。例如，下面是
    [length] 的另一种实现： *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** 请证明 [fold_length] 的正确性。（提示：知道 [reflexivity] 的化简力度比 [simpl]
    更大或许会有所帮助。也就是说，你或许会遇到 [simpl] 无法解决但 [reflexivity]
    可以解决的目标。） *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (fold_map)  

    我们也可以用 [fold] 来定义 [map]。请完成下面的 [fold_map]。 *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** 在 Coq 中写出 [fold_map_correct] 来陈述 [fold_map] 是正确的，然后证明它。
    （提示：再次提醒，[reflexivity] 的化简力度比 [simpl] 更强。） *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_fold_map : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, advanced (currying)  

    在 Coq 中，函数 [f : A -> B -> C] 的类型其实是 [A -> (B -> C)]。
    也就是说，如果给 [f] 一个类型为 [A] 的值，它就会给你函数 [f' : B -> C]。
    如果再给 [f'] 一个类型为 [B] 的值，它就会返回一个类型为 [C] 的值。
    这为我们提供了 [plus3] 中的那种偏应用能力。
    用返回函数的函数处理参数列表的方式被称为_'柯里化（Currying）'_，
    它是为了纪念逻辑学家 Haskell Curry。

    反正，我们也可以将 [A -> B -> C] 解释为 [(A * B) -> C]。这叫做
    _'反柯里化（Uncurrying）'_。对于反柯里化的二元函数，
    两个参数必须作为序对一次给出，此时它不会偏应用。 *)

(** 我们可以将柯里化定义如下： *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** 作为练习，请定义它的反函数 [prod_uncurry]，
    然后在下面证明它们互为反函数的定理。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** 举一个柯里化用途的（平凡的）例子，我们可以用它来缩短之前看到的一个例子： *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** 思考练习：在运行以下指令之前，你能计算出 [prod_curry] 和 [prod_uncurry] 的类型吗？ *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, advanced (nth_error_informal)  

    回想 [nth_error] 函数的定义：

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error l' (pred n)
     end.

   请写出以下定理的非形式化证明：

   forall X n l, length l = n -> @nth_error X l n = None
*)
(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** The following exercises explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church.  We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(** 我们来看看如何用这种记法写数。将函数迭代一次应当与将它应用一次相同。
    因此： *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** 与此类似，[two] 应当对其参数应用两次 [f]： *)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** 定义 [zero] 有点刁钻：我们如何“将函数应用零次”？答案很简单：
    把参数原样返回就好。 *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** 更一般地说，数 [n] 可以写作 [fun X f x => f (f
    ... (f x) ...)]，其中 [f] 出现了 [n] 次。要特别注意我们之前定义
    [doit3times] 函数的方式就是 [3] 的邱奇数表示。 *)

Definition three : cnat := @doit3times.

(** 完成以下函数的定义。请用 [reflexivity] 证明来确认它们能够通过对应的单元测试。 *)

(** **** 练习：1 星, advanced (church_succ)  *)

(** Successor of a natural number: given a Church numeral [n],
    the successor [succ n] is a function that iterates its
    argument once more than [n]. *)
Definition succ (n : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* 请在此处解答 *) Admitted.

Example succ_2 : succ one = two.
Proof. (* 请在此处解答 *) Admitted.

Example succ_3 : succ two = three.
Proof. (* 请在此处解答 *) Admitted.

(** [] *)

(** **** 练习：1 星, advanced (church_plus)  *)

(** Addition of two natural numbers: *)
Definition plus (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* 请在此处解答 *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* 请在此处解答 *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* 请在此处解答 *) Admitted.

(** [] *)

(** **** 练习：2 星, advanced (church_mult)  *)

(** Multiplication: *)
Definition mult (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* 请在此处解答 *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* 请在此处解答 *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* 请在此处解答 *) Admitted.

(** [] *)

(** **** 练习：2 星, advanced (church_exp)  *)

(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type.  Iterating over [cnat] itself is usually problematic.) *)

Definition exp (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* 请在此处解答 *) Admitted.

Example exp_2 : exp three zero = one.
Proof. (* 请在此处解答 *) Admitted.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* 请在此处解答 *) Admitted.

(** [] *)

End Church.

End Exercises.

