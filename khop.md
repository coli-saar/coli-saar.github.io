---
layout: default
title: "Language models can learn implicit multi-hop reasoning, but only if they have lots of training data"
authors:
- name: Yuekun Yao
  affiliation: 1
  homepage: https://ykyaol7.github.io/
- name: Yupei Du
  affiliation: 2
  homepage: https://yupei.nl/
- name: Dawei Zhu
  affiliation: 1
- name: Michael Hahn
  affiliation: 1
  homepage: https://www.mhahn.info/
- name: Alexander Koller
  homepage: https://www.coli.uni-saarland.de/~koller/
  affiliation: 1
affiliations:
- id: 1
  name: Saarland University
- id: 2
  name: Utrecht University
---


<center>
    <img src="static/images/khop/intro.png" width="70%" />
</center>


## Abstract

Implicit reasoning is the ability of a language model to solve multi-hop reasoning tasks in a single forward pass, without chain of thought. We investigate this capability using GPT2-style language models trained from scratch on controlled $k$-hop reasoning datasets ($k = 2, 3, 4$). We show that while such models can indeed learn implicit $k$-hop reasoning, the required training data grows exponentially in $k$, and the required number of transformer layers grows linearly in $k$. We offer a theoretical explanation for why this depth growth is necessary. We further find that the data requirement can be mitigated, but not eliminated, through curriculum learning.



## LMs can learn $k$-hop reasoning, but at a large data cost

We first demonstrate that GPT-2 style models trained from scratch are able to solve $k$-hop reasoning tasks, even without explicit intermediate steps. However, this comes at a cost: the number of training examples required increases exponentially with the number of hops $k$​.

<center>
    <img src="static/images/khop/figure1.png" width="70%" />
</center>
## LMs reason through layer-wise lookup, incurring the cost of depth

The second objective is to understand the underlying mechanism by which language models solve the $k$-hop task. We first demonstrate that language models solve such tasks by layer-wise lookup of bridge entities of a $k$-hop query through empirical evidence (e.g. mechanistic interpretability). Building on this finding, we then establish a theoretical lower bound, showing that the model’s depth must grow with $k$ to maintain such layer-wise lookup mechanism.

<center>
    <img src="static/images/khop/figure2.png" width="50%" />
</center>
## Curriculum learning mitigates the data requirement, but doesn't solve it

Finally, we study training strategies to improve the data budget issue. Models mentioned above were trained solely on $k$-hop task, but  $i$-hop ($i < k$) questions should also be available in realistic setups. By exploiting such easier questions as additional training data for $k$-hop task, we demonstrate that curriculum learning significantly mitigates the exponential growth issue, though not eliminate the increase of data budget as $k$ increases. 

<center>
    <img src="static/images/khop/figure3.png" width="40%" />
</center>