# Lambda Reducer in Smalltalk

## Overview
This project implements a **λ-calculus reducer in GNU Smalltalk**.
Given a parser and a class for Lambda expressions in `lambda.st`, we are to create an implementation for the evaluation and reduction of Lambda expressions.

The implementation provides:
- Conversion of λ-expressions to **de Bruijn indices**
- **Applicative-Order Evaluation (AOE)**
- **Normal-Order Reduction (NOR)**
- **η-Reduction (Eta reduction)**
---

## Features
- **`toDeBruijn`** – converts λ-expressions to de Bruijn form 
- **`aoe`, `aoe:steps`** – performs applicative-order (call-by-value) reductions, where `aoe` performs only a single step
- **`nor`, `nor:steps`** – performs normal-order (call-by-name) reductions, where `nor` performs only a single step
- **`eta`, `eta:steps`** – performs η-reduction when applicable, where `eta` performs only a single step.
- Correct handling of substitution in lambda calculus.

## How to Run / Usage
There is two major classes to run this code: LambdaParser and Lambda.
LambdaParser parses the lambda expression in a way the function Lambda can deal with.
Lambda class has all the methods:
1) **`toDeBruijn`**
2) **`aoe`, `aoe:steps`**
3) **`nor`, `nor:steps`**
4) **`eta`, `eta:steps`**

How to run: 
<pre> gst a2.st lambda.st -  </pre>

Example:
<pre> ``` x := LambdaParser parse: '(^x. ^y. (x y z x)) ((^z . z) x) (^y. y) r'. 
          l := Lambda new: x. 
          l aoe. ``` </pre>




The specification of the project was from an assignment in **CS 442 (Winter 2025)** course.
