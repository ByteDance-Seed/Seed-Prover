<div align="center">
 👋 Hi, everyone! 
    <br>
    We are <b>ByteDance Seed team.</b>
</div>

<p align="center">
  You can get to know us better through the following channels👇
  <br>
  <a href="https://team.doubao.com/">
    <img src="https://img.shields.io/badge/Website-%231e37ff?style=for-the-badge&logo=bytedance&logoColor=white"></a>
  <a href="https://github.com/user-attachments/assets/93481cda-a7f3-47f3-b333-fe6b3da86b78">
    <img src="https://img.shields.io/badge/WeChat-07C160?style=for-the-badge&logo=wechat&logoColor=white"></a>
 <a href="Seed研究员 - 小红书">
    <img src="https://img.shields.io/badge/Xiaohongshu-%23FF2442?style=for-the-badge&logo=xiaohongshu&logoColor=white"></a>
  <a href="https://www.zhihu.com/org/dou-bao-da-mo-xing-tuan-dui/">
    <img src="https://img.shields.io/badge/zhihu-%230084FF?style=for-the-badge&logo=zhihu&logoColor=white"></a>
</p>

![seed logo](https://github.com/user-attachments/assets/c42e675e-497c-4508-8bb9-093ad4d1f216)

# <img src="./imgs/logo.png" height="25"> Seed-Prover


This page is used to store the Seed AI4Math group’s research projects, including Seed‑Prover and Delta‑Prover.

- **Seed Prover** Seed‑Prover is the system we officially participated with in the IMO 2025. [Arxiv](https://arxiv.org/abs/2507.23726)
- **Delta prover** Delta‑Prover is a separate project focused on researching test time techniques for generating formal proofs. [Arxiv](https://arxiv.org/abs/2507.15225)

## Seed Prover IMO 2025
Seed Prover solved 4 out of 6 problems in IMO 2025 during the contest, with the following breakdown:
- **Day 1**: Fully solved P2 (geometry) and P3 (number theory), fully solved P1  (combinatorics) after the competition.
- **Day 2**: Fully solved P4 (number theory) and P5 (combinatorics / algebra)

### Details
- P1 (combinatorics) [Lean](SeedProver/imo2025/p1.lean) : Fully proved after the competition, this is not scored by the IMO.
- P2 (geometry) [NL](SeedProver/imo2025/p2_proof.pdf) : Generated and verified in 2 seconds using Seed-Geometry system
- P3 (number theory) [NL](SeedProver/imo2025/p3_proof.pdf) [Lean](SeedProver/imo2025/p3.lean): Solved in 3 days, with a 2000-line formal proof
- P4 (number theory) [NL](SeedProver/imo2025/p4_proof.pdf) [Lean](SeedProver/imo2025/p4.lean): Solved in 3 days, with a 4000-line formal proof
- P5 (combinatorics / algebra) [NL](SeedProver/imo2025/p5_proof.pdf) [Lean](SeedProver/imo2025/p5.lean): Solved in 1 day, with a proof slightly different from known human solutions

P1,3,4,5 are compiled under Lean v4.14.0.

## Citation
```
@misc{chen2025seedproverdeepbroadreasoning,
      title={Seed-Prover: Deep and Broad Reasoning for Automated Theorem Proving}, 
      author={Luoxin Chen and Jinming Gu and Liankai Huang and Wenhao Huang and Zhicheng Jiang and Allan Jie and Xiaoran Jin and Xing Jin and Chenggang Li and Kaijing Ma and Cheng Ren and Jiawei Shen and Wenlei Shi and Tong Sun and He Sun and Jiahui Wang and Siran Wang and Zhihong Wang and Chenrui Wei and Shufa Wei and Yonghui Wu and Yuchen Wu and Yihang Xia and Huajian Xin and Fan Yang and Huaiyuan Ying and Hongyi Yuan and Zheng Yuan and Tianyang Zhan and Chi Zhang and Yue Zhang and Ge Zhang and Tianyun Zhao and Jianqiu Zhao and Yichi Zhou and Thomas Hanwen Zhu},
      year={2025},
      eprint={2507.23726},
      archivePrefix={arXiv},
      primaryClass={cs.AI},
      url={https://arxiv.org/abs/2507.23726}, 
}
```
