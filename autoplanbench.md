---
layout: default
title: "AUTOPLANBENCH: Automatically generating benchmarks for LLM planners from PDDL"
authors:
- name: Katharina Stein
  homepage: https://kastein.github.io/
  affiliation: 1
- name: Alexander Koller
  homepage: https://www.coli.uni-saarland.de/~koller/
  affiliation: 1
affiliations:
- id: 1
  name: Saarland University
paper: https://arxiv.org/abs/2311.09830
code: https://github.com/minecraft-saar/autoplanbench/tree/main
data: https://github.com/minecraft-saar/autoplanbench/tree/main/autoplanbench_dataset
bibtex: |
    @misc{stein2023autoplanbench,
          title={AutoPlanBench: : Automatically generating benchmarks for LLM planners from PDDL}, 
          author={Katharina Stein and Alexander Koller},
          year={2023},
          eprint={2311.09830},
          archivePrefix={arXiv},
          primaryClass={cs.AI}
    }
---

<center>
    <img src="static/images/autoplanbench/autoplanbench2.png" width="50%" />
</center>



## AutoPlanBench

We present **AutoPlanBench**, a tool for **automatically converting classical planning benchmarks from PDDL into natural language** planning tasks. PDDL (Planning Domain Definition Language) planning domains are very popular in the classical AI planning research community and available domains differ with respect to a number of characteristics designed to compare the performance classical planning approaches in different settings.

AutoPlanBench makes these planning tasks available for research on **reasoning and planning with Large Language Models** (LLMs) at a large scale without requiring manual effort or detailed knowledge about PDDL and the domains. We show that the automatically converted planning domains **yield comparable results as manually created** domain descriptions (from Valmeekam et al. 2023: [PlanBench](https://github.com/karthikv792/LLMs-Planning/tree/main/plan-bench)) across different planning domains and LLM planning approaches.
Evaluating LLM planners across a broad range of planning domains, enables us to pinpoint features of planning domains and specific planning problems that make them hard to for LLMs. 

We release the dataset of natural-language conversions of 12 PDDL domains and a small set of NL planning problems for each of them. Additionally, we provide the code for converting more PDDL domains and problems into natural-language planning tasks for LLMs. 

In addition to the code for creating LLM planning problems, we provide the implementation of four different LLM planning approaches as well as the code to automatically generating few-shot examples for these approaches. 


## PDDL to NL Planning Problems

PDDL planning tasks consist of a domain file and a problem file that defines a specific problem instance with respect to the domain. AutoPlanBench converts both the domain PDDL file and problem files into natural language encodings as illustrated below. The details about the LLM-based conversion methodology can be found in our paper.  

**Blocksworld Domain**
<details open>
<summary> 
Blocksworld Example
</summary>

<img src="static/images/autoplanbench/blocksworld_domain_conv.png" width="70%" />


<br>
<br>

<img src="static/images/autoplanbench/blocksworld_problem_conv.png" width="70%" />

</details>

**Visitall Domain**
<details>
<summary>Visitall Example</summary>

<img src="static/images/autoplanbench/visitall_domain_conv.png" width="70%" />


<br>
<br>

<img src="static/images/autoplanbench/visitall_problem_conv.png" width="70%" />

</details>

## LLM Planning Approaches

### Overall Set-up

<img src="static/images/autoplanbench/setup.png" width="50%" />

* **P-LLM**: does the planning, i.e. predicts a complete plan / the next action given the domain and problem descriptions
* **L-LLM**: translates natural language output of the P-LLM back to PDDL
* **Domain Engine**: simulates the world state; outputs an observation for an input action; checks plan validity

### Tested Approaches

|                 | Non-interactive                                                                                   | Interactive                                                                                                                                  |
|-----------------|---------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------|
| **No Thoughts** | *Basic* <br> * one complete plan                                                                  | *Act* <br> * step by step prediction of next action <br> * observation from domain engine                                                    |
| **Thoughts**    | *CoT* <br> * Chain-of-Thought (Wei et al. 2022) <br> * on complete plan <br> * reasoning thoughts | *ReAct* <br> * Yao et al. 2023 <br> * step by step prediction of next action <br> * observation from domain engine <br> * reasoning thoughts |

<details>
  <summary>Full ReAct Example</summary>
  <img src="static/images/autoplanbench/interactive_example/prompt.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step1.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step2.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step3.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step4.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step5.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step6.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step7.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step8.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step9.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step10.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step11.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step12.png" width="70%" />
  

</details>


## LLM Planning Results 

**Metrics**<br>
* Accuracy (Acc): A plan is considered as correct if the goal state is reached with the last predicted step. The Acc<sup>0</sup> metric measures the number of plans that would be correct under the stricter constraint that the generated plan is correct and directly executable, i.e. no non-executable actions are predicted in the interactive approaches.
* Optimal Plan Length Factor (LF): Average length factor of the correct predicted plans compared to the optimal plans (only counting executable actions).


**Results: AutoPlanBench vs. Manual Conversions**<br>
We find that the automatically converted planning domains (APB) yield comparable results as manually created domain descriptions (Manual; from Valmeekam et al. 2023: [PlanBench](https://github.com/karthikv792/LLMs-Planning/tree/main/plan-bench)) across the different planning domains and LLM planning approaches.


<img src="static/images/autoplanbench/comparison_table.png" width="60%" />

**Results: LLM Planning Performance**<br>
Overall, we find that the planning performance differs considerably between the 12 tested domains. While the best LLM planners (ReAct) do well on some planning tasks, many remain out of reach of current search-based planning methods.

<img src="static/images/autoplanbench/additional_domain_table.png" width="80%" />
