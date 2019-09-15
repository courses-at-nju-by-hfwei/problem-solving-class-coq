# 2019-1-coq

## Goal
- 供有兴趣的学生自学
- 作为 Open Topics 素材

## Content
- [ ] Data Types and Naturals (`Basics.v`)
  - [x] Data Types
  - [ ] Naturals
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
- 如果 `Basics.v` 中含有中文，需要修改 `Basic.html` 文件：
  ```
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
  <link href="common/css/sf.css" rel="stylesheet" type="text/css"/>
  ```