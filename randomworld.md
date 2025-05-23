---
layout: default
title: "Procedural Environment Generation for Tool-Use Agents<br>(RandomWorld)"
authors:
- name: Michael Sullivan
  homepage: https://mjs227.github.io/home/
  affiliation: 1
- name: Mereike Hartmann
  homepage: https://mahartmann.github.io/
  affiliation: 1
- name: Alexander Koller
  homepage: https://www.coli.uni-saarland.de/~koller/
  affiliation: 1
affiliations:
- id: 1
  name: Saarland University
paper: https://www.google.com
code: https://github.com/coli-saar/randomworld
bibtex: |
    None (TODO)
---

<center>
    <img src="static/images/randomworld/figure1.png" width="65%" />
</center>

# RandomWorld

We introduce RandomWorld, a pipeline for the procedural generation of tools and tasks for the generation of a virtually unlimited amount of training data for online RL (or SFT) training of tool-use agents. While such pipelines exist, they are comprised of either small or non-interactive (i.e. not callable) tool inventories, and/or non-compositional or linear tasks. This results in training datasets that can teach models to master simpler tool-use benchmarks (e.g. BFCL-V3; Yan et al., 2024), but that fail to satisfactorily improve model performance on benchmarks with more complex tasks: namely, tasks necessitating the non-linear chaining of tool calls in an interactive setting, such as ToolQA (Zhuang et al., 2023), NESTFUL (Basu et al., 2024), AppWorld (Trivedi et al., 2024), etc.

In contrast, the Randomorld pipeline procedurally generates environments that have:

1. *Depth* (of the tool inventory): a large toolset across a diverse assortment of domains, to facilitate the agent's ability to generalize to unseen tools.
2. (Non-linear) *Compositionality*: chainable tools&mdash;and objectives necessitating non-linear tool-chaining&mdash;to emulate complex, real-world tasks.
3. *Interactivity*: intermediate tool outputs that are visible to the agent, allowing the inspection of outputs and (if necessary) correction of the tool-call sequence&mdash;as is possible in many real-world settings.

Models fine-tuned through either RL or SFT with RandomWorld exhibit increased performance on multiple tool-use benchmarks, and set the new SoTA on two NESTFUL metrics. We also show that downstream performance scales with the size of the tool inventory and number of tasks in the training set: this indicates that further training with RandomWorld can further improve performance, without the need for costly human annotation.

# How it Works

### Type System

Tool and environment generation in RandomWorld are guided by its fine-grained type system. We constructed 73 base types: fine-grained subtypes of strings (e.g. *month-name*, *movie-title*, *address*), integers (e.g. *age*, *year*, *spotify-id*), and floats (e.g. *hotel-rating*, *temperature*, *price*), with further sub-type constraints within this set of custom types: for example, *actor-name* is a subtype of *person-name* (which in turn is a subtype of *string*). 

<details open>
<summary>
Type Hierarchy:
</summary>
<center>
  <img src="static/images/randomworld/type_hierarchy.png" width="65%" />
</center>
</details>

For each of these base types, we craft a description, a generator, and a recognizer. Type generators create new instances of that type, and are used to produce automatically-generated tool outputs: for example, the generator for month-name simply samples one of the twelve month names, while the generator for price samples a float between 1 and 5000, rounded to two decimal points. Type recognizers are boolean-valued functions that check if an object belongs to the type in question, and are used for type-checking inputs to randomly-generated tools.

<details open>
<summary>
Examples of Types, Descriptions, and Instances (Sampled from Generators):
</summary>
<center>
  <img src="static/images/randomworld/type_exs.png" width="85%" />
</center>
</details>

We also implemented three type constructors, that allow for the generation of a theoretically unlimited number of types (recognizers/generators/subtype relations for constructed types are automatically inferred from their constituent types):
- *list* : *T* → *T* takes a type *t* and returns the type *list*(*t*) of lists of objects of type *t*
- *dict* : *T* x *T* → *T* takes types *t*, *u* and returns the type *dict*(*t*, *u*) of dictionaries mapping objects of type *t* to objects of type *u*
- *union* : *T* x *T* → *T* takes types *t*, *u* and returns the type *union*(*t*, *u*) of objects of type *t* or *u*

### Tool Creation

We automatically generate tools (LLM-callable functions) in RandomWorld by sampling input types *A<sub>1</sub>*, ..., *A<sub>n</sub>* and output types *B<sub>1</sub>*, ..., *B<sub>m</sub>*, then using an LLM to generate a name and description for a tool *f* : *A<sub>1</sub>* x ... x *A<sub>n</sub>*  →  *B<sub>1</sub>* x ... x *B<sub>m</sub>* (filtering out the unreasonable ones). 

When passed inputs *a<sub>1</sub>*, ..., *a<sub>n</sub>*, the tool returns *b<sub>1</sub>*, ..., *b<sub>m</sub>*, where each *b<sub>i</sub>* is sampled from the type generator for *B<sub>i</sub>*. While the agent is interacting with the environment, we temporarily store input/output pairs ((*a<sub>1</sub>*, ..., *a<sub>n</sub>*), (*b<sub>1</sub>*, ...,*b<sub>m</sub>*)): this ensures that the tool always returns the same output for a given input (from the agent's perspective).

### Task Generation

RandomWorld tasks are synthesized by first generating a sequence of API calls through a type-guided sampling procedure, to create a data structure that we call a *trajectory skeleton*: a sequence of tool calls *f<sub>1</sub>*, ..., *f<sub>n</sub>*, along with annotations indicating the output(s) of the tool(s) *f<sub>m</sub>*, ..., *f<sub>k</sub>* that *f<sub>i</sub>* (*i* > *m*, *k*) takes as input. For example, the non-linear trajectory skeleton below corresponds to the instruction *"how much will the y<sub>0,1</sub>-th and y<sub>0,2</sub>-th most recently-added items in my Amazon cart cost together, if purchased at the lowest-available price?"*

<center>
  <img src="static/images/randomworld/trj_ex.png" width="55%" />
</center>

These trajectory skeletons begin with sampled *user input* type(s) *Y<sub>0,1</sub>*, ..., *Y<sub>0,1</sub>*, which correspond to the value(s) that will be fed to the agent in the instruction: e.g. *"find <ins>comedy</ins> movies on Netflix that last less than <ins>two hours</ins>"*. We add a new tool call to the trajectory skeleton by sampling a tool whose input types are compatible with the types of the variables currently in play: the user input types, along with (variables representing) the output values of each existing tool call in the trajectory skeleton. We continue sampling new tools to add to the trajectory skeleton until the tool call sequence reaches a pre-sampled length, and the output of the last tool call is taken as the value to be returned by the agent to complete the task (the *goal state*).

### Environment Generation

Once the trajectory skeleton has been generated, we sample user input values and compute output values for each tool call in the sequence, thereby populating an *environment*: a data structure that contains tool input/output values, user information (see below), a goal state, and an instruction. After the environment has been populated from a trajectory skeleton, we prompt an LLM to generate an instruction for that environment, given descriptions of each tool in the trajectory, the value(s) of the user input(s), and the trajectory skeleton. We use a filtering mechanism to ensure that the LLM-generated instructions always contain enough information to reach the goal state.

### Agent Interface

RandomWorld is fully compatible with TRL (von Werra et al., 2020) text environments: for evaluation and RL training, we simply create a text environment for each RandomWorld environment, and pass the agent and the RandomWorld environment's tools to the text environment.





# References

Fanjia Yan, Huanzhi Mao, Cheng-Jie Ji, Tianjun Zhang, Shishir G. Patil, Ion Stoica, and Joseph E. Gonzalez. 2024. Berkeley function calling leaderboard.

Yuchen Zhuang, Yue Yu, Kuan Wang, Haotian Sun, and Chao Zhang. 2023. ToolQA: A Dataset for LLM Question Answering with External Tools. *Advances in Neural Information Processing Systems*, 36:50117–50143.

Kinjal Basu, Ibrahim Abdelaziz, Kiran Kate, Mayank Agarwal, Maxwell Crouse, Yara Rizk, Kelsey Bradford, Asim Munawar, Sadhana Kumaravel, Saurabh Goyal, et al. 2024. Nestful: A Benchmark for Evaluating LLMs on Nested Sequences of API Calls. *arXiv preprint arXiv:2409.03797*.

Harsh Trivedi, Tushar Khot, Mareike Hartmann, Ruskin Manku, Vinty Dong, Edward Li, Shashank Gupta, Ashish Sabharwal, and Niranjan Balasubramanian. 2024. AppWorld: A Controllable World of Apps and People for Benchmarking Interactive Coding Agents. In *Proceedings of the 62nd Annual Meeting of the Association for Computational Linguistics (Volume 1: Long Papers)*, 16022–16076.

Leandro von Werra, Younes Belkada, Lewis Tunstall, Edward Beeching, Tristan Thrush, Nathan Lambert, Shengyi Huang, Kashif Rasul, and Quentin Gallouédec. 2020. TRL: Transformer Reinforcement Learning. [https://github.com/huggingface/trl](https://github.com/huggingface/trl).
