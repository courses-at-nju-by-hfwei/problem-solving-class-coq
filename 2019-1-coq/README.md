# 2019-1-coq

## Goal
- 供有兴趣的学生自学
- 作为 Open Topics 素材

## Content
- [ ] Data Types and Naturals (`Basics.v`)
  - [x] Data Types
  - [x] Naturals
  - [x] `destruct`
  - [ ] Exercise
- [ ] Basic Proof Tactics (combined into `Naturals`?)
- [ ] Logic
- [ ] Induction (I)
- [ ] FP: List
- [ ] Induction (II)
- [ ] Set Theory
- [ ] Relation and Lattice

## Usage
(*还不清楚规范流程；还在摸索中。*)

### Generate HTML
以 `Basics.v` 为例:

- `[Compile] => [Compile buffer]`
- `[Compile] => [Make makefile]`
- `coqdoc --html -toc Basics.v`
- 如果 `Basics.v` 中含有中文，需要修改 `Basic.html` 文件:
  - 将 `<head>` 与 `<title>` 之间的
    ```
    <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
    <link href="coqdoc.css" rel="stylesheet" type="text/css" />
    ```
    替换为
    ```
    <meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
    <link href="common/css/sf.css" rel="stylesheet" type="text/css"/>
    ```

  - 在 `</head>` 与 `<body>` 之间添加:
    ```
    <link href="common/jquery-ui/jquery-ui.css" rel="stylesheet">
    <script src="common/jquery-ui/external/jquery/jquery.js"></script>
    <script src="common/jquery-ui/jquery-ui.js"></script>
    <script src="common/toggleproofs.js"></script>
    <link href="common/css/lf.css" rel="stylesheet" type="text/css"/>
    ```

### AutoTest
(*还不清楚如何操作*)

以 `Basics.v` 为例:
- [ ] 缺少 `BasicsTest.v` 与 `BasicsTest.vo`

### AutoGrade
(*还不清楚如何操作*)

以 `Basics.v` 为例:

## TODO
- [ ] 获取 SF 授权