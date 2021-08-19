---
layout: default
---

<div class="home">

<h1>{{ site.subtitle }}</h1>

</div>


Welcome to CSCI 5535 Fall 2021 edition! The objective of this course is to
study the mathematical foundations of computer programs and programming
languages. To understand what we mean by "mathematical foundations", let's
think back to a familiar concept from high school mathematics. Recall that
the equations `3x+2y-1 = 0` and `3y-2x-2 = 0` describe two straight lines
on a Cartesian plane. If you were to plot these lines, you'd see that these
lines *look* quite different; indeed they are literally orthogonal.
However, if I were to ask you to find their slopes, or to tell me where
they intersect the axes, your approach is likely going to be the same for
both the lines. You would treat them as but different instantiations of the
linear equation `ax + by + c = 0` and thereafter use same mathematics to
reason about both. Now consider the equations `y = 3x^2+2x-1` and `y =
2x-1`. This time, not only do the plots of the equations look very
different, but the equations themselves are fundamentally different. Using
their general forms we can even argue that the former -- a quadratic
equation is *more general* or *more expressive* than the latter -- a linear
equation.  

Now let's extend this analogy to programs and programming languages. A
randomly chosen C++ program likely looks a lot different from a Java
program. But are they both *fundamentally* different? If I were to ask you
to show that both C++ and Java programs compute the Fibonacci function, do
you need fundamentally different techniques to prove the same? Or is it
possible to treat them as just different instantiations of a general form
amenable to uniform reasoning? Wouldn't it be great if there exists a
formal mathematics to reason about computer programs that would let us
categorically answer these questions?

Why, there is such a mathematics! The formal study of computer programs as
mathematical objects predates the invention of the modern computer itself,
and continues to this day under the aegis of Programming Languages and
Formal Methods research. This course covers several foundational ideas and
mathematical techniques that have resulted from this effort. In particular,
we are going to study the mathematical abstractions of computer programs
that let us understand the fundamental differences among different
programming styles and languages. We shall develop the reasoning calculi
that let us categorically prove or refute various kinds of assertions about
programs, for instance that a program computes the Fibonacci function. We
are going to see how the concept of a "proof" can be defined to such a
degree of precision that a *machine* can check if the proof we write is
correct or incorrect. In fact we go so far as to only consider such
*mechanized proofs* as real proofs in this course. And whats more, we shall
also learn proof automation techniques that let us program a machine to
*generate* a proof rather than just check it! These and more exciting
things are going to be the topics of our classroom discussions this semester.

## Classroom and Office Hours

* **Instructor:** [Gowtham Kaki](http://gowthamk.github.io).
* **Where:** ECCS 1B14 
* **When:** M,W,F 3:00 - 3:50 PM
* **Office Hours**: On [Piazza](https://piazza.com/class/kjw3pah6lmo1hv) or by appointment.

## Textbook

* We are largely going to use [Volume 1](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) (Logical Foundations) and [Volume 2](https://softwarefoundations.cis.upenn.edu/plf-current/index.html)
  (Programming Language Foundations) of Pierce et al's [Software Foundations](https://softwarefoundations.cis.upenn.edu/) course notes.
* We will refer to Chlipala's [Certified Programming With Dependent
  Types](http://adam.chlipala.net/cpdt/) occasionally.
* Pierce's [Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) is a recommended reading. This book is available for checkout at [CU Libraries](https://ebookcentral.proquest.com/lib/ucb/detail.action?docID=3338823).

## Evaluation Components

| Item                |    Nos.  | Weight (%) |
|---------------------|----------|--------------:|
| Homeworks           |  8 of 10 |     40        |
| Course Project      |     1    |     25        |
| Final               |     1    |     35        |
