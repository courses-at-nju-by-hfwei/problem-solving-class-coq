# problem-solving-class-coq
Rock on Coq for the Problem Solving Class at Nanjing University

## Contents
- [2019-1-coq](https://github.com/hengxin/problem-solving-class-coq/tree/master/2019-1-coq)
- [ ] [2019-2-coq]()
- [ ] [2019-3-coq]()
- [ ] [2019-4-coq]()

## Usage
(*还不清楚规范流程；还在摸索中。*)

### Generate HTML
以 `Basics.v` 为例:

- `[Compile] => [Compile buffer]` in CoqIDE
- `[Compile] => [Make makefile]` in CoqIDE
- `coqdoc --html -toc Basics.v`
  - 如果含有中文，则使用 `coqdoc --html --utf8 -toc Basics.v`

### AutoTest
(*还不清楚如何操作*)

以 `Basics.v` 为例:
- [ ] 缺少 `BasicsTest.v` 与 `BasicsTest.vo`

### AutoGrade
(*还不清楚如何操作*)

以 `Basics.v` 为例:

### Makefile
如何生成以及使用 Makefile 自动编译

## TODO
- [x] CoqIDE 安装指南
- [ ] CoqIDE 使用手册
- [ ] 获取 SF 授权
- [ ] CoqDoc 斜体/粗体
