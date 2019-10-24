(** * 数据类型与自然数 (Data Types and Naturals) *)

(**
  - 请勿公开发布习题解答
  - 有问题请在 http://problemoverflow.top/ 提问
*)

(* ################################################################# *)
(** * 引言 *)

(** 
  '算法 + 数据结构 = 程序' 
  (Algorithms + Data Structures = Programs) by Niklaus Wirth.
  
  如果说算法是一张食谱，那么数据就是食材。
  所谓'巧妇难为无米之炊'，没有数据，算法就无用武之地。
  正如食材各式各样，数据也有各种 _'类型'_
  (在本教材中，我们使用数据类型的说法，而不是数据结构)。
  
  数据类型包含两部分含义： 
  - 数据 (也称 _'值'_) 构成的集合； 
  - 定义在这些数据上的操作。
  
  比如自然数是一种数据类型，它的数据集合是 {0, 1, 2, ...}，
  它允许的操作包括前驱、后继、加法、减法 (受限的减法)、乘法、幂运算等。
  
  同样重要的是，自然数作为一种数据类型，它 _'不包括'_ -1、0.5、2/3、e 等数据，
  也_'不支持'_除法、拼接、旋转等操作。
  
  在程序设计语言里， _'类型检查'_ (Type Checking) 的工作就是检查：
  - 是否使用了无效的 (invalid) 数据； 
  - 是否进行了非法的 (unsupported) 操作。

  本章介绍如何在 Coq (内置的 _'Gallina'_ 程序设计语言) 中定义数据类型。
  同时，本章还将介绍如何在 Coq 中做证明。
  我们以自然数数据类型为例。
*)
(* ################################################################# *)
(** * 数据与函数 *)

(**
  Coq 的标准库 (Standard Library) 中内置了一些常用的数据类型，
  比如布尔类型、自然数、列表、散列表等。
  
  要定义一个数据类型，我们需要：
  - 定义数据集合
  - 定义操作
*)

(* ================================================================= *)
(** ** 枚举类型 *)

(* ================================================================= *)
(** *** 一周七日 *)

(** 
  以下声明 (Declaration) 定义了一个名为 [day] 的数据类型。
  它的数据构成的集合为 {[monday], [tuesday], [wednesday], 
  [thursday], [friday], [saturday], [sunday]}。
  [day] 是 _'枚举'_ (Enumerate) 数据类型，
  因为我们直接在定义中一一列举了它包含的值。
*)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(**
  下面，我们定义一个名为 [next_day] 的操作，也称为函数。
  该操作接受一个类型为 [day] 的数据 [d] (称为_'参数'_ (parameter))，
  返回一个类型为 [day] 的数据 (称为_'返回值'_ (return value))。 
*)

Definition next_day (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end.

(** 
  [next_day saturday] 的结果应该是 [sunday]。
  我们可以用 [Compute] 指令查看该结果。
*)
Compute (next_day saturday).
(* ==> sunday : day *)

(**
  [(next_day (next_day saturday)) = (next_day sunday) = monday.] Sad!
*)
Compute (next_day (next_day saturday)).
(* ==> monday : day *)

(** 第二，我们通过单元测试 (Unit Test) 检验函数。
  下面的 [Example] 定义了一个断言 (Assertioin):
  [saturday] 的明天的明天是 [monday]。
  我们还给这个断言起了个名字： [time_files]。
  以后，我们可以使用 [time_files] 引用该断言。
*)
Example time_flies:
  (next_day (next_day saturday)) = monday.

(**
  我们需要 _'证明'_ 该断言是真的。
  证明很简单，分为两步：
  
  证明：
  - 化简。等号左边的 [(next_day (next_day saturday))] 可以化简为 [monday]。
  - 相同性判断。等号左边的 [monday] 与 等号右边的 [monday] 相同。
  证毕。
*)
Proof. simpl. reflexivity. Qed.

(**
  Coq 是 _'交互式定理证明'_ (Interactive Theorem Proving; ITP) 工具，
  也称为 _'证明助手'_ (Proof Assistant)。
  
  要想使用 Coq 证明某个定理，你需要：
  - 清楚该定理的证明过程
  - 清楚 Coq 支持的证明策略 (Proof Tactics)
  - 将证明过程翻译成 Coq 支持的证明策略
  
  比如上例中的 [simpl] 表示化简，[reflexivity] 判断相同性。
  [Proof] 表示证明开始，[Qed] 表示证毕 (哇，多么美妙的词语)。
*)
(* ================================================================= *)
(** *** 布尔类型 *)

(** 下面的声明定义了布尔类型 [bool]，它包含两个值 [true] 与 [false]。*)

Inductive bool : Type :=
  | true
  | false.

(** 
  常用的布尔函数包括： [negb] (取反)； [andb] (并且)； [orb] (或者)。
*)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** 
  我们以 [orb] 为例进行“单元测试”与证明。
  这四个测试用例实际上构成了 [orb] 的真值表 (Truth Table)。
  
  注意： [orb] 函数接受两个 [bool] 类型的参数。
  [orb true false] 表示将函数 [orb] 应用 (Apply) 到参数 [true] 与 [false] 上。
*)

Example test_orb1:  (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity. Qed.

(** 我们可以使用 [Natation] 为布尔函数引入更常见的符号。*)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** **** 练习：1 星, standard (nandb) *)

(**
  要想熟练使用 Coq，不做练习是不可能的。
  
  现在，你需要定义一个布尔函数 [nandb]:
  只有当两个参数都是 [true] 时，它才返回 [false];
  否则，它返回 [true]。
  你可以使用之前定义过的布尔函数 [negb]、[andb]、[orb]。
  
  指令 [Admitted] 是证明中的占位符。
  你的任务就是将它替换成真正的证明。
*)

Definition nandb (b1:bool) (b2:bool) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_nandb1: (nandb true false) = true.
(* 请在此处解答 *) Admitted.
Example test_nandb2: (nandb false false) = true.
(* 请在此处解答 *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* 请在此处解答 *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* 请在此处解答 *) Admitted.
(** [] *)
(* ================================================================= *)
(** ** 类型 *)

(** 
  Coq 中的每个表达式都有类型。我们可以使用 [Check] 指令查看表达式的类型。
*)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** 
  Coq (内置的 _'Gallina'_ ) 是 _'函数式'_ (Functional) 程序设计语言。
  在函数式程序设计语言中，函数也是数据，也有类型。
  更多关于函数式程序设计的内容，我们会在后续课程与 Coq 教材中学习。
  
  函数 [negb] 的类型是 _'函数类型'_ [bool -> bool]。
  这是由 [bool] 类型构成的复合类型，
  它告诉我们： [negb] 是一个函数，它接受一个 [bool] 类型的参数，
  返回一个 [bool] 类型的值。
*)

Check negb.
(* ===> negb : bool -> bool *)

(** 
  类似地，[andb] 的类型是 [bool -> bool -> bool]，
  它告诉我们：[andb] 是一个函数，它接受两个 [bool] 类型的参数，
  返回一个 [bool] 类型的值。
  
  关于 [bool -> bool -> bool] 的另一种“更函数式的”理解方式，
  我们将在函数式程序设计章节中介绍。
  此处仅简单提及。
  实际上，[->] 运算符是右结合的。
  也就是说，[bool -> bool -> bool] 实际上是 [bool -> (bool -> bool)]。
  它告诉我们：[andb] 是一个函数，它接受一个 [bool] 类型的参数，
  返回一个类型为 [bool -> bool] 的函数 
  (没错，在函数式程序设计中，函数可以作为返回值。是不是很优雅？)。
  这个返回的函数又可以接受一个 [bool] 类型的参数，返回一个 [bool] 类型的值。
*)
Check andb.
(* ===> negb : bool -> bool -> bool *)
(* ================================================================= *)
(** ** 由旧类型构造新类型 *)

(** 
  在现实生活中，问题层出不穷。
  不同的问题可能使用不同的数据类型。
  我们不希望每次都从头构造一个数据类型，而是希望能基于已有的数据类型定义新的数据类型。
*)

(** [rgb] 仍然是简单的枚举类型。*)
Inductive rgb : Type :=
  | red
  | green
  | blue.

(**
  [color] 与我们之前定义的数据类型不同。
  除了我们已经熟悉的 [black]、[white] 形式之外，
  它还包含 [primary (p : rgb)]。
*)
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(** 
  这里，我们需要介绍一点理论知识。(很简单，不要害怕。)
  
  [Inductive color : Type] 告诉 Coq：
  _'归纳'_ (Inductively) 地定义 (也称 _'构造'_) 名为 [color] 的数据类型。
  
  在归纳定义中，我们需要给出构造 [color] 类型的数据的方法 (也称 _'构造函数'_)：
  - [black] 是一个构造函数。它表示 [black] 是类型为 [color] 的值。
  - [white] 是一个构造函数。它表示 [white] 是类型为 [color] 的值。
  - [primary (p : rgb)] 是一个构造函数。
    它表示，如果 [p] 是类型为 [rgb] 的值，
    那么 [primary p] 就是类型为 [color] 的值。
    例如，[primary red]、[primary green]、[primary blue]
    都是类型为 [color] 的值。
  
  同样重要的是，[Inductive color : Type] 还告诉 Coq：
  类型为 [color] 的值有且 _'仅有'_ 以上三种构造方式。
  例如，[sunday]、[primary saturday]、[primary false] 
  都不是类型为 [color] 的值。
*)

(** 
  在定义函数时，我们可以针对每个构造函数使用 _'模式匹配'_ (Pattern Match)。
  函数 [monochrome] 接受一个类型为 [color] 的参数 [c]。
  根据上面的分析，[c] 有且仅有三种可能的构造方式。
  [match] 分别考虑这三种构造方式：
  - [black] 只可能与 [black] 匹配。
  - [white] 只可能与 [white] 匹配。
  - [primary q] 只可能与 [primary xxx] 匹配。
  这里，[q] 为变量，它的类型是 [rgb] (Coq 可以自动推断出这一点)。
  当 [primary q] 与 [primary xxx] 匹配时，[q] 被 _'绑定'_ (bind) 到 [xxx]。
  你可以在 [=>] 的右边使用 [q]。
  在本例中，我们并没有在 [=>] 的右边使用 [q]。
  在这种情况下，我们可以使用通配符 [_] 代替 [q]。
*)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

(**
  我们还可以对 [primary q] 进行更细致的模式匹配。
  函数 [isred] 中的 [primary _] 用于匹配除 [primary red] 之外的由
  [primary] 构造的 [color]，即 [primary green] 与 [primary blue]。
*)
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* ================================================================= *)
(** ** 模块 *)

(**
  Coq 使用 _'模块'_ (Module) 组织较大规模的代码。
  目前，我们只需要了解它的两种基本功能:
  - 可以将一组紧密相关的定义放在 [Module X] 和 [End X] 之间。
    这样，在 [End X] 之后，我们可以使用 [X.foo] 引用模块内部的 [foo]。
  - [Module X] 与 [End X] 中的定义是封闭的。
    它们不会与该模块外部的同名定义产生冲突。
  
  这里，我们使用了模块的第二种功能，
  在 [Module NatPlayground.] 里定义自己的 [nat] 类型。
  注意: 在 [End NatPlayground.] 之后，我们采用的仍是 Coq 标准库里提供的定义。
*)
Module NatPlayground.
(* ================================================================= *)
(** ** 自然数 (Naturals) *)

(**
  现在，我们要定义自然数数据类型。好戏刚刚开场。
  
  自然数类型与之前我们定义的数据类型有一个很大的区别，
  那就是自然数有无穷多个 (在后续课程中，我们会知道，自然数有可数无穷多个)。
  我们无法以一一列举的方式定义自然数类型。
  怎么办？怎么才能在有限的纸张上写下无穷多个自然数？
  
  答案是：归纳定义。[Inductive]关键词的威力在这里得以显现。
*)

Inductive nat : Type :=
  | O
  | S (n : nat).

(**
  So Easy! 我们来解读一下。
  
  这个归纳定义告诉我们，自然数 [nat] _'有且仅有'_ 两种构造方式：
  - [O] 是一个构造函数。
  它告诉我们，[O] 是自然数。(注意：这里是大写字母 [O]，不是数字 [0]。
  本质上讲，我们现在仅仅是在定义一些符号。这些符号毫无意义。
  它们的意义来自于我们如何使用(通过定义函数)它们。
  如果我们像使用自然数那样使用它们，那么它们“就是”自然数。)
  - [S (n : nat)] 是一个构造函数。
  它告诉我们，如何 [n] 是自然数，那么 [S n] 也是自然数。
  
  需要注意的是，与 [monochrome] 中的 [primary q] 构造函数不同，
  [S n] 中的 [n] 的类型是我们正在定义的 [nat]。
  什么？等等！你要定义 [nat]，但是你在定义中又用到了 [nat]，这不会造成循环依赖吗?
  让我们再分析一下 [nat] 的定义。
  根据第一个构造函数，我们知道 [O] 是自然数 (类型是 [nat])。
  根据第二个构造函数，我们知道 [S O] 是自然数。
  再根据第二个构造函数，我们知道 [S (S O)] 是自然数，
  依此类推，我们知道 [S (S (S O))]、[S (S (S (S O)))]…… 都是自然数。
  
  综上所述，在 [nat] 的定义中，
  第一个构造函数给出了一个特定的自然数 [O]，
  第二个构造函数根据已知的自然数 [n] 构造一个新的自然数 [S n] 
  (也称为 [n] 的 _'后继'_ (Successor))。
  没有循环依赖。
*)

(** 
  需要再次强调的是，到目前为止，我们仅仅是定义了一些符号：
  [O]、[S O]、[S (S O)] 等。
  [O]、[S] 并无特别之处，你可以将它们换成其它符号。
  
  接下来，我们将在 [nat] 上定义函数：
  前驱函数 [pred]、加法 [plus]、减法 [minus]、乘法 [mult] 与幂运算 [exp]。
  正是这些函数为符号赋予了意义。
  (以后大家在学习数理逻辑的时候，遇到的第一个难点，
  就是区分语法 (符号、公式)与语义 (解释、意义、真假)。)
*)
End NatPlayground.

(** 
  [nat] 实际上刻画了自然数的一进制表示法。
  在一进制下，100 需要表示为一百个S后接一个O。
  为了避免这种麻烦，Coq 允许我们将一进制的 [nat] 解析打印为十进制形式。
*)

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
Check 4.

(** 你猜构造函数 [S] 的类型是什么？ *)
Check S.

Module NatPlayground2.
(**
  先定义前驱函数 [pred]。
  需要注意的是，我们规定 [O] 的前驱仍是 [O]。
  根据 [nat] 的定义，我们知道非零自然数的形式一定是 [S n']，
  它的前驱是 [n']。 
*)
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(**
  函数 [plus] 返回两个自然数 [n] 与 [m] 的和：
  - 第一个分支： [O + m = m]
  - 第二个分支： [S n' + m = S (n' + m)]。
  注意：我们还没有定义 “+”。这里的 “+” 是数学上的加法符号。
*)  
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(**
  需要注意的是，[plus n m] 使用了自身 [plus n' m] (n' < n)，
  是一个递归函数。
  因此，我们使用了关键字 [Fixpoint]，
  而不是之前在定义函数时使用的 [Definition]。
  
  [Fixpoint] 是与递归定义紧密相关的概念。
  这里，我们不深究它背后的理论。
  有兴趣的同学，可以选修冯老师的课程或者研究生关于计算理论的课程。 
*)

(** 
  此时，有同学提问：使用关键词 [Definition] 与 [Inductive] 定义函数有什么区别?
  答：注意观察 CoqIde 后侧的 "Messages" 窗口。
  除了 "plus is defined"，
  它还显示了一行信息:
  "plus is recursively defined (decreasing on 1st argument)"。
  Coq 要求所有函数都是可计算的 (在这里，你可以理解成函数对于所有输入都会终止)。
  要保证这一点，Coq 要求使用 [FixPoint] 定义的递归函数中的某些参数必须是递减的。
  
  Coq 检查到 [plus] 的第一个参数是递减的。
  这意味着我们对参数 [n] 执行了_'结构化递归'_ (Structural Induction)。

  然而，不存在算法能够判断所有的递归定义的函数是否是可终止的
  (又是神奇的计算理论!)。
  对此，你的新朋友 Coq 也无能为例。
  因此，有些时候我们需要告诉 Coq 一些信息，帮助 Coq 验证某个递归函数确实是可以终止的
  (我们暂时不需要做这些)。
*)

(** 测试 [3 + 2]。 *)
Compute (plus 3 2).

(** 为得出此结论，Coq 所执行的化简步骤如下： *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))] 根据第二个 [match] 子句
==> [S (S (plus (S O) (S (S O))))] 根据第二个 [match] 子句
==> [S (S (S (plus O (S (S O)))))] 根据第二个 [match] 子句
==> [S (S (S (S (S O))))]          根据第一个 [match] 子句 *)

(**
  乘法 [mult] 的定义方式类似，它用到了刚刚定义的 [plus]。
  这里，[(n m : nat)] 的意思与 [(n : nat) (m : nat)] 相同。
*)
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(** **** 练习：1 星, standard (exp)  
  我们将自然数上的幂运算的定义作为练习。
  你需要用到刚刚定义的 [mult]。
*)

Fixpoint exp (base power : nat) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** 测试一下。*)    
Example test_exp: (exp 3 3) = 27.
Proof. (* 请在此处写入证明 *) Admitted.

(** 你可以在两个表达式之间添加逗号来同时匹配它们
  减法 [minus] 的定义稍微有些复杂。
  它需要对两个参数 [n] 与 [m] 分别做模式匹配。
*)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** **** 练习：1 星, standard (exp)  
  注意 [minus] 是如何使用 [match] 对两个参数同时做并列模式匹配的。
  当然，你也可以先对 [n] 做模式匹配，再嵌套地对 [m] 做模式匹配。
  留作练习。
*)
Fixpoint minus' (n m:nat) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
  
Example test_minus': minus 10 5 = minus' 10 5.
Proof. (* 请在此处写入证明 *) Admitted.
(** [] *)
End NatPlayground2.

(**
  我们可以引入通常的加法、减法、乘法 _'记号'_ (Notation)。
  [level] 规定了优先级，[left associativity] 表示“左结合”。
  目前，你不需要了解这些细节。
*)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(** **** 练习：1 星, standard (factorial)
    请定义阶乘函数 [factorial]：
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n > 0)
*)
Fixpoint factorial (n:nat) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_factorial1:          (factorial 3) = 6.
(* 请在此处解答 *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (double_plus)
  完成函数 [double] 的定义，它接受参数 [n]，返回 [2n]。
  请使用递归定义方式，而不是定义为 [n + n]。 
*)

Fixpoint double (n : nat) : nat
  (* := 你的解答 *).
Admitted.
(** [] *)

(** **** 练习：2 星, standard (sum_to)
  完成函数 [sum_to] 的定义，它接受参数 [n]，返回 [1 + 2 + ... + n]。 
*)
Fixpoint sum_to (n : nat) : nat
  (* := 你的解答 *).
Admitted.
(** [] *)
  
Example sum_to_10 :
  sum_to 10 = 55.
Proof. (* 请在此处解答 *) Admitted.

(** 我们再来练习定义几个自然数上的函数。*)

(** [eqb] 判断两个自然数是否相等 (命名中的后缀 ”b“ 表示它返回的是 bool 值)。*)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(** **** 练习：1 星, standard (eqb1)
  参考 [minus]的定义，使用并列模式匹配改写 [eqb]，并设计测试用例。
*)
Fixpoint eqb1 (n m : nat) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
  
(** 
  [evenb] 判断给定的自然数 [n] 是否为偶数。
  尽管我们知道 [O] 为偶数，但是我们无法直接判断 [S n'] 是否为偶数，
  因为 [S n'] 是否为偶数，取决于 [pred n'] 是否为偶数。
  换句话说，我们需要 _'递归'_ (Recursively) 定义该函数。
  并且，根据上面的分析，我们需要两个 _'基础情况'_ (Basic Cases):
  [O] 是偶数，[S O] 不是偶数。
*)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Example test_evenb1:   evenb 2019 = false.
Proof. simpl. reflexivity. Qed.

(** 我们可以基于 [evenb] 定义 [oddb]。*)
Definition oddb (n:nat) : bool := 
  negb (evenb n).

Example test_oddb1:    oddb 2019 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 9102 = false.
Proof. simpl. reflexivity.  Qed.

(** 
  [leb] 函数检查第一个参数 [n] 是否小于等于第二个参数 [m]。
  注意这也是一个递归函数。
*)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** 为 [eqb] 与 [leb] 引入符号记法。*)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3':  (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** 练习：1 星, standard (ltb)  
    [ltb] 检查第一个参数 [n] 是否小于第二个参数 [m]。
    请完成它的定义。 
*)
Definition ltb (n m : nat) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
(* 请在此处解答 *) Admitted.
Example test_ltb2:             (ltb 2 4) = true.
(* 请在此处解答 *) Admitted.
Example test_ltb3:             (ltb 4 2) = false.
(* 请在此处解答 *) Admitted.
(** [] *)
(* ################################################################# *)
(** * 基于化简的证明 *)

(** 
  我们已经定义好了自然数类型。
  下面，我们要正式进入另一个主题：证明。
  在 Coq 中，我们不仅可以编程，我们还可以做证明。
  学习如何做证明是问题求解课程的核心内容之一。
  
  有同学问：为什么要在 Coq 中学习证明？
  在数学课上学习证明不就够了吗？
  
  如果你做过足够长、足够复杂的证明，你就会体会到，证明是多么容易出错。
  证明出了错，要想找到错误，又是何等困难。
  如果在你写证明的时候，能有一位严苛的权威人士始终盯着你的证明，
  帮助你检查每一个证明步骤，直到 [Qed] 的那一美妙时刻，
  你是不是会对写出来的证明更有信心？
  
  Coq 就是这么一位严苛的权威人士。
  你可以欺骗你自己，但是你欺骗不了 Coq。
  从今往后，你将与 Coq 相爱相杀。
*)

(**
  本节从三个最基本的 _'证明策略'_ (Proof Tactics) 开始：
  [intros] [simpl] 与 [reflexivity]。
  - [intros] 用于引入变量。
  - [simpl] 用于化简。
  - [reflexivity] 用于判断等号两边是否相同。
 
  证明策略是在证明过程中，你下达给 Coq 的指令。
  Coq 将执行这些指令。
  如果执行不下去，就意味着你的证明行不通，需要改换思路。
*)

(**
  定理 [plus_O_n] 说明：[0] (即，[O]) 是自然数加法的左单位元。
  - [Theorem] 表明这是一个需要证明的定理。
    [Theorem] 这个关键字本身并不重要，可以是 [Example]、[Lemma]、[Fact]等。
  - [plus_O_n] 是定理的名字。以后，你可以通过这个名字引用该定理。
  - [forall] 是一阶谓词逻辑里的全称量词符号，读作“对于所有”。
*)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. (* 证明开始 *)
  intros n. (* 引入任意自然数 [n] *)
  simpl. (* 等号两边化简 *)
  reflexivity. (* 等号两边相同 *)
Qed. (* 证毕 *)

(** 
  我们逐步解释该证明：
  - [Proof.]：证明开始。
  - [intros n.]：我们要证明的定理是一个全称命题：“对于所有的自然数 [n]，……”。
    在证明这类命题时，通常的做法是：“假设 [n] 是任意自然数，……”。
    在后续的证明“……”中，我们就可以使用 [n] 了。
    也就是说，我们将 [n] 从 _'证明目标'_ (Goal) 
    移到了 _'证明上下文'_ (Context) 中。
    [intros n.] 的作用就是“引入任意自然数 [n]”。
    (两年以后，面对《数理逻辑十二讲》的第四讲，
    小明将会回想起问题求解习题课带他见识Coq证明的那个睡意惺忪的清晨。)
  - [simpl.]：根据加法 [plus] 的定义 (模式匹配的第一种情况)，
    等号左边 [0 + n] 可以化简为 [n]。
  - [reflexivity.]： 等号左右两边都是 [n]。
  - [Qed.]：证毕。
*)

(**
  实际上，[reflexivity] 在判断等号两边是否相同时，
  会先尝试对等号两边进行化简。
  因此，有些时候，[simpl] 可以省略。
*)
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.
  
(**
  类似地，我们可以证明定理 [mult_0_l]：[0] 是自然数乘法的左零元。
  (定理名中的后缀 [_l] 表示 left。)
*)
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.

(**
  请解释定理 [plus_1_l] 及其证明过程。
  (你要确保理解每一个证明步骤。这次没有 Coq 盯着你。
  你可以欺骗我，但你不能欺骗你自己。)
*)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.
(* ################################################################# *)
(** * 基于改写 (Rewriting) 的证明 *)
(** _'改写'_ (Rewriting) 指的是用等号的一端替换等号的另一端。*)

(**
  定理 [plus_id_example] 读作：
  对于所有的自然数 [n] 与 [m]，
  如果 [n = m]，那么 [n + n] = [m + m]。
  
  首先，这个定理是一个条件句：如果 A，那么 B。
  要证明这类结论，我们通常是将 A 作为已知条件，然后证明 B 成立。
  用 Coq 的语言来讲，就是把 A 从待证目标 (Goal) 移到上下文 (Context) 中。
  我们又需要用到 [intros] 策略。
*)
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* 将两个量词移到上下文中： *)
  intros n m.
  (* 将前提 [n = m] 移到上下文中，并命名为 [H]： *)
  intros H.
  (* 用前提 [H : n = m] 改写目标，即将目标中的 [n] 替换成 [m]： *)
  rewrite -> H.
  (* 替换后，目标中的等号两边相同，都为 [m + m] *)
  reflexivity.
Qed.

(** 
  [rewrite -> H] 策略中的箭头 [->] 表示从左往右应用 Rewriting，
  即在目标中，将等式 [H] 的左边 (即，[n]) 替换成等式 [H] 的右边 (即，[m])。
  如果要改变 Rewriting 的方向，则使用 [<-] 箭头。
  
  另外，[rewrite H] 默认为 [rewrite -> H]。
*)

(** **** 练习：1 星, standard (plus_id_exercise)
  删除 "[Admitted.]"，完成定理 [plus_id_exercise] 的证明。
  ([Admitted] 表示暂时跳过该定理的证明，而将其将其作为已知条件。) 
*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(**
  如前所述，_'改写'_ (Rewriting)' 指的是用等号的一端替换等号的另一端。
  这里的等式可以是之前证明过的定理。
  比如定理 [mult_O_plus] 的证明用到了之前证明过的 [plus_O_n]。
  
  (是不是已经忘记了 [plus_O_n] 说了些什么？没关系，这很正常。
  这些都是为了教学构造出来的没有多大实际意义的例子。
  忘了的话，就试试 [Check plus_O_n]。)
*)
Check plus_O_n.
(** => forall n : nat, 0 + n = n. *)

Theorem mult_O_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  (* 将两个量词移到上下文中： *)
  intros n m.
  (* 将目标中的 [0 + n] 替换为 [n] *)
  rewrite -> plus_O_n.
  (* 改写后，得到 [n * m = n * m] *)
  reflexivity.
Qed.

(** 
  需要注意的是，[plus_O_n] 是关于 [n] 的全称语句。
  在 Rewriting 时，Coq 会通过匹配当前的证明目标来尝试
  _'实例化'_ (Instantiate) [n]。 *)
    
(** **** 练习：2 星, standard (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  (* 请在此处解答 *) 
Admitted.

(** [] *)
(* ################################################################# *)
(** * 分情形分析 (Case Analysis) 证明法 *)

(** 
  不用想也知道，使用 [simpl]、[reflexivity]、[rewrite]
  只能证明一些 “Too Simple，Sometimes Naive” 的定理。
  我们需要学习更高级的证明策略。
  
  先尝试使用已学过的证明策略证明下述定理。
  你会发现 [simpl] 不起作用。
  这是因为，[n + 1] 中的 [n] 是任意自然数。
  在 [plus] 的定义中，Coq 无法确定使用哪一条模式匹配进行化简。
*)
Print Nat.add. (** 与 [plus] 相同 *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.  (* 无能为力! *)
Abort. (* 使用 [Abort] 放弃证明。*)

(** 
  解决的方法也很自然：对 [n] 分情况分析。
  - 如果 [n = O]：使用 [plus] 的第一条模式匹配进行化简。
  - 如果 [n = S n']：使用 [plus] 的第二条模式匹配进行化简。

  对自然数 [n] 进行分情况分析，
  用 Coq 的语言来讲，就是 [destruct n]。 
*)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. reflexivity.
Qed.

(** 
  由于 [nat] 的定义中包含两个构造函数，
  所以，[n] 有两种构成方式。
  在使用 [destruct n] 分情况分析时，Coq 会产生两个子目标，
  分别对应 [n = O] 与 [n = S n'] 两种情况。
  
  记号 "[as [ | n'] eqn:E]" 使用 [|] 区分了两种情况，
  并将每种情况下与 [n] 有关的等式命名为 [E]。
  在第一种情况中，[E] 为 [n = O]。
  由于 [O] 构造函数没有参数，所以 [ | n'] 中 [|] 的左边为空。
  在第二种情况中，[E] 为 [n = S n']。
  其中，[n'] 是 [ | n'] 中的 [n']，对应于构造函数 [S] 的参数。 

  另外，在上面的证明中，我们使用并列的两个 [-] 标记了两种情况，
  使得证明的结构更为清晰。
  从语法上讲，[-] 并不是必须的。
  但是，强烈建议大家在使用 [destruct] 策略时，同时使用 [-]。
  如果需要嵌套地分情况分析，可以使用 [+]、[*]、[{}] 等 (我们马上就会碰到)。
*)

(**
  [destruct] 策略可用于任何归纳 (Inductive) 定义的数据类型。
  定理 [negb_involutive] 的证明使用 [destruct] 对布尔值分情况分析。 
*)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(** 
  注意：我们省略了 [destruct] 的 [as] 子句。
  我们可以写 [as [|]] 或者 [as []]。
*)

(** [destruct] 可以嵌套使用。*)
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. 
  destruct b eqn:Eb. (* 对 [b] 分情况分析 *)
  - destruct c eqn:Ec. (* 在 [b = true] 的情况下，嵌套地对 [c] 分情况分析 *)
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec. (* 在 [b = false] 的情况下，嵌套地对 [c] 分情况分析 *)
    + reflexivity.
    + reflexivity.
Qed.

(** 我们也可以用匹配的花括号区别每个子目标对应的证明。*)
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. 
  destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } } (* 程序员有两种，一种将右花括号如此放置，还有一种将右花括号放在下一行*)
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** 此外，花括号有限定范围的作用，它允许我们在一个证明中的多个层级下使用同一种标号： *)
Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. 
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(** 
  在很多证明中，我们在引入变量之后会立即对该变量进行情况分析。
  例如： intros x y. destruct y as [|y] eqn:E.
  Coq 提供了一种简便的记法： intros x [|y].
  也就是说，我们可以在引入变量的同时对它进行情况分析。
  (在 Coq 的术语中，这被称为 _'intro pattern'_。)
  
  需要注意的是，上述简便记法丢失了 [eqn:E] 信息。
*)

Print eqb.
Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - simpl. reflexivity.
Qed.

(** 如果没有需要命名的参数，我们只需写 [[]]。 *)
Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** 练习：2 星, standard (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：1 星, standard (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (andb_eq_orb)  
    请证明定理 [andb_eq_orb]。
    可能有一点点难度 (是不是很兴奋？)，试试看吧。
*)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* 请在此处解答 *)
Admitted.
(** [] *)
(* Fri Jul 19 00:32:19 UTC 2019 *)
