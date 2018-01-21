# Spring 2018

Class meetings are Tuesdays and Thursdays 9:30-10:45 in ECEE 283.

All students should have received a welcome e-mail from me on how to get set up with the course tools. If you did not receive such a message, please send me an e-mail. All further correspondence will be via Piazza.

## Instructor

![Bor-Yuh Evan Chang](assets/chang.jpg) | [Prof. Bor-Yuh Evan Chang](http://www.cs.colorado.edu/~bec) <br/> **Regular Office Hours**: Tue and Thu 8:30am-9:20am in CSEL ECCS 112.

## Co-Instructor

![Matthew A. Hammer](assets/hammer.png) | [Prof.  Matthew A. Hammer](http://matthewhammer.org) <br/> **Regular Office Hours**: Tue 2:30pm-3:20pm and Wed 9:30am-10:30am in CSEL ECCS 112.

# Course Overview

This course introduces the fundamental principles behind modern programming
language design, semantics, and implementation.  Ultimately, you should come
away with the ability to apply foundational programming language ideas and
techniques to your own projects.

The course has two broad topics:
- Introduction to Semantics and Type Systems: How do we describe programming
  languages? And which programs "make sense"?
- Research Applications: Students will have the opportunity to consider other
  related topics of interest in the form of a course project, most often in the
  form of a survey of recent research on a topic of interest.

The first part of this graduate-level course focuses on the dynamic and static
semantics of a variety of programming language features (e.g., "what does a
function really mean?"). We will study structural operational semantics as a way
to formalize the intended execution and implementation of languages. Operational
semantics concepts and notation are widely used in modern programming language
research. We will survey axiomatic semantics, which provides a basis for
verifying programs. Axiomatic semantics underlie research efforts in formal
verification and bug finding (e.g., [SLAM](http://research.microsoft.com/slam/),
which led to Microsoft's [Static Driver
Verifier](http://www.microsoft.com/whdc/devtools/tools/sdv.mspx)). We will
briefly look at denotational semantics as a prelude to abstract interpretation.
Abstract interpretation also underlie research efforts in program analysis and
bug finding (e.g., [Astrée](http://www.astree.ens.fr/), which has been used by
Airbus to analyze their flight control software). 

The last part of the course covers special topics drawn from research in areas
such as applications of program semantics to program analysis and verification.

For more on the course philosophy, see [Why Study Programming Languages?](https://www.cs.cmu.edu/~rwh/courses/ppl/phil.html) by Robert Harper.

# Prerequisites

The prerequisites for this course are programming and mathematical experience
with several different programming languages (e.g., C, ML, Java) with diverse
computational models (i.e., imperative **and** functional), which may be
satisfied by taking [CSCI
3155](http://www.cs.colorado.edu/courses/csci3155.html) or equivalent. The ideal
programming experience is experience implementing language tools, which may be
satisfied by taking an undergraduate compilers course (e.g., [CSCI
4555](http://www.cs.colorado.edu/courses/csci4555.html)). The ideal mathematical
experience is familiarity with mathematical logic and the ability to construct
rigorous proofs (in particular by structural induction). Your desire to be
exposed to this material is _very important_. 

Advanced undergraduates may consider taking this course after talking with the
instructor. 

If you have not already taken these courses or if you have any concerns, please
talk with the instructor. Proficiency in programming and mathematical logic is absolutely expected. This means that you should be able to pick up a new programming language with relative ease and are reasonably comfortable with inductive thinking.

# Requirements

You will be responsible for the following:

*   **[Class Participation](assignments.html#participation)** (5%). Participation includes both in-class and online discussion.
*   **[Homework Assignments](assignments.html#homework)** (35%). There will be homework assignments for the first part of course. This is a project-based course, so assignments will be the main learning vehicle.
*   **A Final Exam** (30%).
*   **[A Final Project](assignments.html#projects)** (30%). In the second part of the course, your time will be spent on a final project. You will create a final project that explores, extends, or experiments with the ideas in the course.
*   **Reading**. There will be required papers or book chapters to read.

## Grading

Your overall grade will be determined using the ratio for homework assignments, exercises, the midterm exam, the final exam, and class participation shown above.  There is no predetermined curve (i.e., I hope everyone gets an A based on the level of mastery demonstrated).

## Regrades

Any concern about an error in grading must be submitted within **one week** of when it is returned. Any coursework submitted for reconsideration may be regraded in its entirety, which could result in a lower score if warranted.  To request a regrade, please go to the instructor's office hours with your coursework and an explanation of what you believe the grading error to be.

## Make-Up Exam Policy

There will be no special or make-up examinations for any student (except in the case of emergency or the stated [special accommodations](#special-accommodations)).

## Redo Policy

This course is project-based, which means the learning is driven primarily by the homework assignments.  To encourage iteration until mastery, you may "redo" any assignment via an oral interview with the instructor for a maximum of 90%. A "redo" must be completed within **one week** of when the assignment is returned. You may request one interview per assignment. However, you may discuss your solutions with the instructors in office hours as much as you like before requesting your regrade. You must submit your assignment on time to participate in a "redo".

## Extra Credit and Participation

Extra credit opportunities may be offered during the course semester.  Extra credit is recorded separately from normal grades and are only considered after final grades have been calculated.  If your final grade is just below a grade cutoff, extra credit may bump you up to the next grade. Finding a bug in the course materials that is then adopted is a standing offer for extra credit.

## Pair Programming

You may sometimes be asked to work on homework assignments in **pairs**, enabling pair programming. Homework assignments are the main opportunity to learn material in this course and thus they count for a relatively small portion of your final grade. It is strongly advised that you work on all the problems in an assignment together so that you understand all of the material and are prepared for the exam.  Everyone will submit assignments, and you must cite your partner explicitly.  If necessary, you may switch partners between assignments, and you are responsible for all assignments individually (e.g., if your partner drops the course midway though an assignment, you still need to submit on time).

## Workload

This is a masters-level project-based course. A high level of independent learning is expected.

# Evaluation

Both your ideas and also the clarity with which they are expressed matter—both in your English prose, your mathematical writing, and your code!

We will consider the following criteria in our grading:

*   _How well does your submission answer the questions_? For example, a common mistake is to give an example when a question asks for an explanation. An example may be useful in your explanation, but it should not take the place of the explanation.
*   _How clear is your submission_? If we cannot understand what you are trying to say, then we cannot give you points for it. Try reading your answer aloud to yourself or a friend; this technique is often a great way to identify holes in your reasoning. For code, not every program that "works" deserves full credit. We must be able to read and understand your intent. Make sure you state any preconditions or invariants for your functions (either in comments or as assertions)

# Integrity of the Course Materials

The development effort in the course materials, including the lab assignments, the exercises, and the exams, is significant. You agree that you will not share any course materials publicly or privately outside of your teams. The course materials, include your or anyone else's solutions to the lab assignments, exercises, and exams. In particular, you agree not to post your solutions to the lab assignments in a public source code repository, such as public Github repositories. Please use private source code repositories for your work.

Note that there is no conflict with the [Collaboration Policy](#collaboration-policy) described below. You are welcome and encouraged to support each other in the learning of the material.

# Collaboration Policy

You are welcome and encouraged to work together in learning the material. If you worked with someone on an assignment, or if your submission includes quotes from a book, a paper, or a web site, you should thank the source. Bottom line, feel free to use resources that are available to you as long as the use is **reasonable** and you **cite** them in your submission. However, **copying answers directly or indirectly from solution manuals, web pages, or your peers is certainly unreasonable**. If you have any doubts in this regard, please ask the course staff.

You are allowed to discuss homework assignments with other students. However, in order to ensure that the work you submit is still your own, we insist that you adhere to a _whiteboard policy_ regarding these discussions: you are not allowed to take any notes, files, or other records away from the discussion. For example, you may work on the homework at the whiteboard with another student, but then you must erase the whiteboard, go home, and write up your solution individually. We take your ability to recreate the solution independently as proof that you understand the work that you submit.

This policy is our attempt to balance the tension between the benefits of group work and the benefits of individual work. We ask that you obey the spirit of the policy, as well as the letter: ensure that all work you submit is your own and that you fully understand the solution. This is in your best interest: the exam constitutes a significant part of your final grade and it will draw heavily on the terminology, concepts, and techniques that are exercised in the homework. It is unlikely that you will be able to do well on the exam if you do not take full advantage of the learning opportunity afforded by the homework assignments.

**Academic Dishonesty Policy**. We will go by the [Honor Code](http://honorcode.colorado.edu) set forth by the University:

> All students enrolled in a University of Colorado Boulder course are responsible for knowing and adhering to the [academic integrity policy](http://www.colorado.edu/policies/academic-integrity-policy) of the institution. Violations of the policy may include: plagiarism, cheating, fabrication, lying, bribery, threat, unauthorized access, clicker fraud, resubmission, and aiding academic dishonesty. All incidents of academic misconduct will be reported to the Honor Code Council ([honor@colorado.edu](mailto:honor@colorado.edu); 303-735-2273). Students who are found responsible for violating the academic integrity policy will be subject to nonacademic sanctions from the Honor Code Council as well as academic sanctions from the faculty member. Additional information regarding the academic integrity policy can be found at [honorcode.colorado.edu](http://honorcode.colorado.edu).

Academic sanctions may include, but is not limited to, a zero for the assignment or a failing grade for the course.

# Course Communication

There are two main websites for this course.
- **Public**. This public course website contains the course syllabus (this page), the reading schedule, and assignment links. The public website is your primary source for learning materials.
- **Private**. The [course moodle](https://moodle.cs.colorado.edu/course/view.php?id=828) contains any links that are limited to enrolled students. From the moodle, you will find resources like the discussion forum, private project repositories, submission links, grades, feedback, and interview sign-ups. The instructor will provide the enrollment key.

# Texts 

- Robert Harper. [Practical Foundations for Programming Languages](http://www.worldcat.org/title/practical-foundations-for-programming-languages/oclc/840012058).
- Glynn Winskel. [The Formal Semantics of Programming Languages](http://www.worldcat.org/isbn/9780262731034).

# Supplemental Readings

The following are some other recommended resources:

- Benjamin C. Pierce. [Types and Programming Languages](http://www.worldcat.org/isbn/0262162091). [[e-book via CU library](http://libraries.colorado.edu/record=b3750188~S3)]

# Distance Learning

This course is also offered through distance education. All assignment
submission and content delivery will be electronic.

## Deadlines

Distances students will follow the same assignment deadlines as in-class students. Content delivery should be essentially immediate. Exceptions will only be made in the case of extreme technical difficulties in publishing content.

# Course Tools and External Links

## Moodle

We will use Moodle for grades and protected resources. If you do not already have an account, please create one and join the course moodle. The enrollment key is in the welcome e-mail.

## Piazza

We will be using Piazza for online, outside-of-class discussion, which is accessed via the course moodle. Rather than emailing questions to the teaching staff, questions should be posted on the course piazza. I encourage you to make class-wide posts whenever possible, but there is an option to send an instructor-private message. You also have the option of posting anonymously.

## Off-Campus Access

The CU library has instructions for [off-campus access](http://ucblibraries.colorado.edu/research/offcampusaccess.htm) to certain online resources (e.g., ACM Digital Library).

## OCaml

The programming languages we study and use in this course will be closely related to [ML](https://en.wikipedia.org/wiki/ML_(programming_language)). Specifically, we will use the [OCaml](http://ocaml.org/) implementation for homeworks that involve programming assignments.

- [OCaml](http://caml.inria.fr/ocaml/index.en.html) is available for most platforms and via most package management systems. I suggest installing OCaml using an appropriate package manager on your system (e.g., MacPorts or Homebrew on Mac OS and Cygwin on Windows).
- [OCaml Manual](http://caml.inria.fr/pub/docs/manual-ocaml/index.html)
- [Developing Applications with Objective Caml](http://caml.inria.fr/pub/docs/oreilly-book/) (book)
- [99 Problems](https://ocaml.org/learn/tutorials/99problems.html) in OCaml
- [ocaml.org/learn](https://ocaml.org/learn/) is an overview of learning resources
- IDE: [Emacs mode](http://tuareg.forge.ocamlcore.org/), [Eclipse plug-in](http://www.algo-prog.info/ocaide/)

## Computing

For a Linux environment, the following are some resources:

- Get the [CU CS Virtual Machine](https://foundation.cs.colorado.edu/vm/)
- Get a [CSEL account](https://csel.cs.colorado.edu/) (if you're enrolled in a CSCI course). CSEL has a lab in ECCS 128 and remote access servers with SSH (`elra-01` through `elra-04.cs.colorado.edu`).

# Classroom Behavior

We trust and expect everyone to behave in a civil and courteous manner.

In class, the course staff promises their undivided attention and reciprocally expects the same from you. In today's world, this promise requires **turning off transmitting devices**, such as cell phones and wi-fi on notebook computers. The use of notebook computers should be discussed with the instructor and they should be used only for purposes directly relevant to the class discussion. Please notify the course staff if you encounter behavior that distracts from your learning.

We will also go by the policies set forth by the University:

> Students and faculty each have responsibility for maintaining an appropriate learning environment. Those who fail to adhere to such behavioral standards may be subject to discipline. Professional courtesy and sensitivity are especially important with respect to individuals and topics dealing with differences of race, color, culture, religion, creed, politics, veteran's status, sexual orientation, gender, gender identity and gender expression, age, disability, and nationalities. Class rosters are provided to the instructor with the student's legal name. I will gladly honor your request to address you by an alternate name or gender pronoun. Please advise me of this preference early in the semester so that I may make appropriate changes to my records. For more information, see the policies on [classroom behavior](http://www.colorado.edu/policies/student-classroom-and-course-related-behavior) and the [student code](http://www.colorado.edu/osc/sites/default/files/attached-files/studentconductcode_16-17-a.pdf).

# Sexual Misconduct, Discrimination, Harassment and/or Related Retaliation

We will go by the policies set forth by the University:

> The University of Colorado Boulder (CU Boulder) is committed to maintaining a positive learning, working, and living environment. CU Boulder will not tolerate acts of sexual misconduct, discrimination, harassment or related retaliation against or by any employee or student. CU's Sexual Misconduct Policy prohibits sexual assault, sexual exploitation, sexual harassment, intimate partner abuse (dating or domestic violence), stalking or related retaliation. CU Boulder's Discrimination and Harassment Policy prohibits discrimination, harassment or related retaliation based on race, color, national origin, sex, pregnancy, age, disability, creed, religion, sexual orientation, gender identity, gender expression, veteran status, political affiliation or political philosophy. Individuals who believe they have been subject to misconduct under either policy should contact the Office of Institutional Equity and Compliance (OIEC) at 303-492-2127\. Information about the OIEC, the above referenced policies, and the campus resources available to assist individuals regarding sexual misconduct, discrimination, harassment or related retaliation can be found at the [OIEC website](http://www.colorado.edu/institutionalequity/).

# Disability Accommodations

We will go by the [disability guidelines](http://www.colorado.edu/disabilityservices) set forth by the University:

> If you qualify for accommodations because of a disability, please submit to your professor a letter from Disability Services in a timely manner (for exam accommodations provide your letter at least one week prior to the exam) so that your needs can be addressed. Disability Services determines accommodations based on documented disabilities. Contact Disability Services at 303-492-8671 or by e-mail at [dsinfo@colorado.edu](mailto:dsinfo@colorado.edu). If you have a temporary medical condition or injury, see the [Temporary Injuries](http://www.colorado.edu/disabilityservices/students/temporary-medical-conditions) guidelines under the Quick Links at the [Disability Services](http://www.colorado.edu/disabilityservices/) website and discuss your needs with your professor.

# Religious Observances

We will go by the [policy for religious observances](http://www.colorado.edu/policies/fac_relig.html) set forth by the University:

> Campus policy regarding religious observances requires that faculty make every effort to deal reasonably and fairly with all students who, because of religious obligations, have conflicts with scheduled exams, assignments, or required attendance. we will try to accommodate religious conflicts in a reasonable manner. Please check the [exam dates](schedule.html) and submit all requests for adjustments within the **first four weeks** of class. See the [campus policy regarding religious observances](http://www.colorado.edu/policies/observance-religious-holidays-and-absences-classes-andor-exams) for full details.

# Acknowledgments

This course is developed in collaboration with [Prof. Matthew A. Hammer](http://matthewhammer.org) and is based on materials from [Prof. Robert Harper](http://www.cs.cmu.edu/~rwh/) at Carnegie Mellon University, [Prof. George Necula](http://www.cs.berkeley.edu/~necula/) at the University of California, Berkeley, and [Prof. Westley Weimer](https://web.eecs.umich.edu/~weimerw/) at the University of Michigan.
