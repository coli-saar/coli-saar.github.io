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
    <img src="static/images/randomworld/figure1.png" width="50%" />
</center>

# RandomWorld

We introduce RandomWorld, a pipeline for the procedural generation of tools and tasks for the generation of a virtually unlimited amount of training data for online RL (or SFT) training of tool-use agents. While such pipelines exist, they are comprised of either small or non-interactive (i.e. not callable) tool inventories, and/or non-compositional or linear tasks. This results in training datasets that can teach models to master simpler tool-use benchmarks (e.g. BFCL-V3; Yan et al., 2024), but that fail to satisfactorily improve model performance on benchmarks with more complex tasks: namely, tasks necessitating the non-linear chaining of tool calls in an interactive setting, such as ToolQA (Zhuang et al., 2023), NESTFUL (Basu et al., 2024), AppWorld (Trivedi et al., 2024), etc.

In contrast, the Randomorld pipeline procedurally generates environments that have:

1. *Depth* (of the tool inventory): a large toolset across a diverse assortment of domains, to facilitate the agent's ability to generalize to unseen tools.
2. (Non-linear) *Compositionality*: chainable tools&mdash;and objectives necessitating non-linear tool-chaining&mdash;to emulate complex, real-world tasks.
3. *Interactivity*: intermediate tool outputs that are visible to the agent, allowing the inspection of outputs and (if necessary) correction of the tool-call sequence&mdash;as is possible in many real-world settings.






# References

Fanjia Yan, Huanzhi Mao, Cheng-Jie Ji, Tianjun Zhang, Shishir G. Patil, Ion Stoica, and Joseph E. Gonzalez. 2024. Berkeley function calling leaderboard.

Yuchen Zhuang, Yue Yu, Kuan Wang, Haotian Sun, and Chao Zhang. 2023. ToolQA: A Dataset for LLM Question Answering with External Tools. *Advances in Neural Information Processing Systems*, 36:50117–50143.

Kinjal Basu, Ibrahim Abdelaziz, Kiran Kate, Mayank Agarwal, Maxwell Crouse, Yara Rizk, Kelsey Bradford, Asim Munawar, Sadhana Kumaravel, Saurabh Goyal, et al. 2024. Nestful: A Benchmark for Evaluating LLMs on Nested Sequences of API Calls. *arXiv preprint arXiv:2409.03797*.

Harsh Trivedi, Tushar Khot, Mareike Hartmann, Ruskin Manku, Vinty Dong, Edward Li, Shashank Gupta, Ashish Sabharwal, and Niranjan Balasubramanian. 2024. AppWorld: A Controllable World of Apps and People for Benchmarking Interactive Coding Agents. In *Proceedings of the 62nd Annual Meeting of the Association for Computational Linguistics (Volume 1: Long Papers)*, 16022–16076.
