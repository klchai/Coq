# SOFTWARE FOUNDATIONS
[![License: CC BY-NC-SA 4.0](https://img.shields.io/badge/License-CC%20BY--NC--SA%204.0-lightgrey.svg)](http://creativecommons.org/licenses/by-nc-sa/4.0/)
![Mathinfoly](http://www.mathinfoly.org/assets/img/logo/logomathinfoly2.png)</br></br>
This repository contains:
1. **Coq scripts** (.v files) for the Software Foundations electronic textbook.
2. **Solutions** of all exercises.
3. **Slides** in .html format.

## Table of Contents

- [Background](#background)
- [Install](#install)
- [Abstract](#abstract)
- [Book](#book)
- [Slides](#slides)
- [Extra](#extra)

## Background
Course at Summer School on Cryptography, Blockchain and Program Verification [Mathinfoly 2019](http://www.mathinfoly.org/)
at INSA Lyon on 27-31 August 2019. </br></br>
**Teaching Team**: [Cătălin Hriţcu](http://prosecco.gforge.inria.fr/personal/hritcu/), [Roberto Blanco](https://robblanco.github.io/), [Florian Groult](https://github.com/floriangru), [Jérémy Thibault](http://perso.eleves.ens-rennes.fr/people/Jeremy.Thibault/), [Exequiel Rivas](https://dcc.fceia.unr.edu.ar/~erivas/), and various local helpers.

## Install
This project uses [Coq](https://coq.inria.fr/). Go check them out if you don't have them locally installed. Compile each file `<filename>.v` by using `coqc -Q . LF <filename>.v`.

## Abstract
This course will give a gentle introduction to: 
1. logic and proofs
2. functional programming
3. program verification

The most interesting aspect of this course is the use of the Coq proof assistant to write functional programs and to prove
logical theorems about these programs, in a way that is one hundred percent formalized and machine-checked. 
</br></br>
The course will follow the 1st half of the Logical Foundations book (i.e., Volume 1 of the [Software Foundations](https://softwarefoundations.cis.upenn.edu/) series). </br></br>
The students will learn the most by solving Coq exercises, from very simple to more interesting ones. </br></br>
The course will also give an overview of the practical successes of functional programming (e.g., the Tezos blockchain implementation is written in OCaml) and of verification in proof assistants like [Coq](https://coq.inria.fr/) (from machine-checked proofs of mathematical results such as the 4-color theorem to the CompCert verified compiler). </br></br>
We will end with an introduction to the Curry-Howard correspondence, a deep and beautiful connection between functional programs and logical proofs, which lies at the heart of the Coq proof assistant.

## Book
- We will follow a slightly modified version of the Logical Foundations book, which is available [here](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/index.html).
- Chinese Version is available [here](https://coq-zh.github.io/SF-zh/lf-current/index.html).

## Slides
- Tuesday, 27 August 2019:
   + 14h00--16h00 Lecture: Motivation ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/Motivation.pdf)), [Basics](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Basics.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/Basics.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Basics.v)), [Induction](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Induction.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/Induction.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Induction.v))

- Wednesday, 28 August 2019:
   + 9h00--10h30 Exercises Basic + Induction
   + 11h00--12h30 Lecture: [Lists](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Lists.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/Lists.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Lists.v)), [Poly](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Poly.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/Poly.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Poly.v)), [Tactics](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Tactics.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/Tactics.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Tactics.v))

- Thursday, 29 August 2019:
   + 9h00--10h30 Exercises Lists + Poly + Tactics
   + 11h00--13h00 Lecture: [Logic](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Logic.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/Logic.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/Logic.v))
   + 15h00--16h30 Lecture: [IndProp](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/IndProp.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/IndProp.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/IndProp.v))

- Friday, 30 August 2019:
   + 9h00--10h30 Exercises Tactics + Logic + IndProp
   + 11h00--12h00 Lecture: [ProofObjects](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/ProofObjects.html) ([slides](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/slides/ProofObjects.html), [exercises](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/ProofObjects.v))

## Extra
If you are interested in verifying functional programs **with effects**, have a loof at [F*](https://www.fstar-lang.org).
