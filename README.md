# SOFTWARE FOUNDATIONS

This repository contains:
1. **Coq scripts** (.v files) for the Software Foundations electronic textbook.
2. **Solutions** of all exercises.
3. **Slides** in .html format.

## Table of Contents

- [Background](#background)
- [Install](#install)
- [Abstract](#abstract)
- [Book](#logicalfoundationsbook)

## Background
Course at Summer School on Cryptography, Blockchain and Program Verification [Mathinfoly 2019](http://www.mathinfoly.org/)
at INSA Lyon on 27-31 August 2019. </br></br>
**Teaching Team**: [Cătălin Hriţcu](http://prosecco.gforge.inria.fr/personal/hritcu/), [Roberto Blanco](https://robblanco.github.io/), [Florian Groult](https://github.com/floriangru), [Jérémy Thibault](http://perso.eleves.ens-rennes.fr/people/Jeremy.Thibault/), [Exequiel Rivas](https://dcc.fceia.unr.edu.ar/~erivas/), and various local helpers.

## Install
This project uses [Coq](https://coq.inria.fr/). Go check them out if you don't have them locally installed.
compile each file <filename>.v by using `coqc -Q . LF <filename>.v`.

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

## Logical Foundations Book
We will follow a slightly modified version of the Logical Foundations book, which is available [here](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/book/lf-current/index.html).
