# Delamano

This is the source code for a web platform made with the objective of helping second semester CS students at Universidad de los Andes with their discrete math class. 

It does so by giving them practice exercises related to the subject, letting them input the steps they belive would solve those exercises, and checking if those steps are correct or not. Given the location of Universidad de los Andes, a significant part of the website is written in Spanish.

It was inspired by [ADAM's](https://adam.math.hhu.de/) Lean Game Server, and thus shares its licence.

## Stack (that I coded with)

* Typescript, React, Redux
* Lean4

## The platform

<br><img src="https://github.com/user-attachments/assets/125a2626-6644-419a-96a4-8ef00673d897" aspect-ratio="1/1" width="60%"/><br>

On the landing page, the student can choose the topic they want to learn (it is important to remind again that the selection of topics is based on Universidad de los Andes' syllabus). 

<br><img src="https://github.com/user-attachments/assets/50e9dfae-29c9-4d8c-afbf-7942e7c4f285" aspect-ratio="1/1" width="60%"/><br>

Once the student selects the topic, worlds (the big circles) and levels (the small circles) will show. Each small circle is an exercise as the ones they have to solve for the class. 

<br><img src="https://github.com/user-attachments/assets/bb688ffd-1e98-4727-9f77-5852f6d7679f" aspect-ratio="1/1" width="60%"/><br>

Inside a level, the student will find three big blocks of UI. In the middle block, there is all the info related with the exercise to be solved. The left block is full with tips to solve the exercise, and the right with the theorems that the student can use.

<br><img src="https://github.com/user-attachments/assets/b8d9fd21-d145-4ff4-af6c-805d81ffacc1" aspect-ratio="1/1" width="30%"/><br>

Inputing, for example, "definicion_implicacion" in the shown exercise, will make the proof advance to a new state. Once the student has inputed a sequence of logical steps that reduce the state of the proof to a tautology, the platform will tell the student that the steps are correct. Thus, allowing them to study in moments where assistance is not available. 

## Running the project

To run the project, there are a few non-common dependencies have to be installed:

* [Lean4](https://github.com/leanprover/lean4): a proof programming language really useful to proove theorems. Can be installed with Vscode. 
* [Elan](https://github.com/leanprover/elan): **in case you want to run Lean4 without Vscode**, a tool for managing Lean4 installations.

Furthermore, you have to build the levels of the platform for it to work. You can chose to do it with `npm build_games`, but the same library would be installed in all of the games subfolders. To avoid this, you can select which game to build (check how with the definition of the `build_games` command).

Once build, simply run `npm start` to run the development version of the site, and play with it. 
