# A formally proven data structures library intended for Formal Methods teaching

**Update: This project has now been graded with a mark of 74%.**

### Why this project ?

In order to complete my MSc in software engineering at Oxford Brookes university in 2015/2016 I had to realize an original research project related to my course. Earlier in this year I took a module explaining the concepts of formal methods, a set of techniques used, in the field of sofware engineering, to prove the correctness of a software towards a specification.

There is many ways to assess and try to achieve this goal, for instance using functional testing along with a specification written in english or using unit/integration tests written by the developers. Formal methods are another approach to help producing bug-free software using (most of the time) mathematically-based specifications along with an automated theorem prover. 

I found this concept very interesting since a mathematical specification leaves much less space for interpretation than an english-based (or any other language) specification and therefore could lead to fewer mistakes (different interpretations, missing edge cases, etc...) in testing protocols. This is the reason why I decided to study this domain further in my MSc dissertation.

The subject I choose was initially proposed by Dr. Ian Bayley, Senior lecturer in Computing at Oxford Brookes University. The main goal was to provide a set of formally proven data structures in order to help the future students undertaking the formal software engineering module to have a better understanding of the field and its usages.

In this repository you will find the [final report](https://github.com/AlexisChevalier/formal-data-structure-library/blob/master/Papers/Final%20report.pdf) of my dissertation and the [short paper](https://github.com/AlexisChevalier/formal-data-structure-library/blob/master/Papers/Short%20paper.pdf) if you are only interested in an overview of my research and implementation process. You will also find the source code (implemented using the [Dafny language](https://github.com/Microsoft/dafny)). 

### Project overview

Many details on the implementation choices and process are explained in the final and short reports, I strongly encourage you to read them and eventually look at the references I used to work on this project. The main choice that was made was the [Dafny language](https://github.com/Microsoft/dafny), the project was initially planned to be implemented using [Spec#](https://specsharp.codeplex.com/), but the Dafny project was more active and featured a completely new language dedicated to formal verification.

The following data structures were chosen and nearly all of them were fully implemented, validated and tested:

| Data structure / Algorithm | Validated | Tested | Comments |
|:---------------------:|:---------:|:-----:|:-----------------------------------------------------------------------------:|
|	SimpleStack			| Yes 		| Yes 	| Generic |
|	ArrayStack			| Yes 		| Yes 	| Generic |
|	LinkedListStack		| Yes 		| Yes 	| Generic |
|	LinkedListQueue		| Yes 		| Yes 	| Generic	|
|	ArrayList 			| Yes 		| Yes 	| Generic |
|	KeyValue LinkedList | Yes 		| Yes 	| Generic for values only, not keys |
|	TreeMap				| Yes 		| Yes 	| Generic for values only, not keys |
|	HashMap				| Partly* 	| Yes* 	| Generic for values only, not keys; * Validated and tested using assumptions	|
|	BubbleSort			| Yes 		| Yes 	| Not generic |	
|	InsertionSort		| Yes 		| Yes 	| Not generic |	

The testing and validation process was made in two main steps:
- The first one simply used the Dafny automated prover to assess the correctness of the implementation towards the mathematical specification
- The second one was a simple test case used to assess the behavior of the implementation because even if the mathematical specification has been respected, it could be incorrect and not match the expectations of the system

If you wish to have more informations about the project, please read the [final report](https://github.com/AlexisChevalier/formal-data-structure-library/blob/master/Papers/Final%20report.pdf) or at least the [short paper](https://github.com/AlexisChevalier/formal-data-structure-library/blob/master/Papers/Short%20paper.pdf) of my dissertation.

### Requirements

This is a Visual Studio 2012 project, in order to work correctly it also requires the Dafny extension available at https://github.com/Microsoft/dafny/wiki/INSTALL.

You can also use the Dafny web IDE (http://rise4fun.com/Dafny) or the command line interpreter provided by the Dafny project.

The Dafny source files are located in the DafnyLib\Libraryfolder.

### Support and contributions

I don't plan to actively support this repository for the moment since I have other full-time professional activitites. I will however answer questions if I can and if I find enough time (please use the Github issue system so that everyone can benefit from the discussions).

### Licence

This project is licenced under the MIT licence because I want the licence to be as permissive as possible, I encourage you to use it and improve it if you find it useful!
