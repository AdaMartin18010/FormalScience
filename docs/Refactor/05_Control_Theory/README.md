# 控制理论

## 目录结构

```
05_Control_Theory/
├── README.md                    # 主目录文件
├── 01_Basic_Concepts/          # 基本概念
├── 02_Linear_Control/          # 线性控制
├── 03_Nonlinear_Control/       # 非线性控制
├── 04_Optimal_Control/         # 最优控制
├── 05_Robust_Control/          # 鲁棒控制
├── 06_Adaptive_Control/        # 自适应控制
├── 07_Intelligent_Control/     # 智能控制
├── 08_Distributed_Control/     # 分布式控制
├── 09_Networked_Control/       # 网络控制
├── 10_Quantum_Control/         # 量子控制
└── 11_Synthesis/               # 综合理论
```

## 1. 基本概念 (01_Basic_Concepts)

### 1.1 控制系统基础
- [1.1.1 控制系统定义](./01_Basic_Concepts/01_Control_System_Definition.md)
- [1.1.2 系统建模](./01_Basic_Concepts/02_System_Modeling.md)
- [1.1.3 系统分析](./01_Basic_Concepts/03_System_Analysis.md)
- [1.1.4 系统设计](./01_Basic_Concepts/04_System_Design.md)

### 1.2 数学基础
- [1.2.1 微分方程](./01_Basic_Concepts/05_Differential_Equations.md)
- [1.2.2 拉普拉斯变换](./01_Basic_Concepts/06_Laplace_Transform.md)
- [1.2.3 状态空间](./01_Basic_Concepts/07_State_Space.md)
- [1.2.4 传递函数](./01_Basic_Concepts/08_Transfer_Function.md)

### 1.3 系统性质
- [1.3.1 稳定性](./01_Basic_Concepts/09_Stability.md)
- [1.3.2 可控性](./01_Basic_Concepts/10_Controllability.md)
- [1.3.3 可观性](./01_Basic_Concepts/11_Observability.md)
- [1.3.4 性能指标](./01_Basic_Concepts/12_Performance_Indices.md)

## 2. 线性控制 (02_Linear_Control)

### 2.1 线性系统理论
- [2.1.1 线性系统基础](./02_Linear_Control/01_Linear_System_Basics.md)
- [2.1.2 线性时不变系统](./02_Linear_Control/02_Linear_Time_Invariant_Systems.md)
- [2.1.3 线性时变系统](./02_Linear_Control/03_Linear_Time_Varying_Systems.md)
- [2.1.4 线性离散系统](./02_Linear_Control/04_Linear_Discrete_Systems.md)

### 2.2 经典控制
- [2.2.1 PID控制](./02_Linear_Control/05_PID_Control.md)
- [2.2.2 根轨迹法](./02_Linear_Control/06_Root_Locus_Method.md)
- [2.2.3 频率响应法](./02_Linear_Control/07_Frequency_Response_Method.md)
- [2.2.4 奈奎斯特判据](./02_Linear_Control/08_Nyquist_Criterion.md)

### 2.3 现代控制
- [2.3.1 状态反馈控制](./02_Linear_Control/09_State_Feedback_Control.md)
- [2.3.2 观测器设计](./02_Linear_Control/10_Observer_Design.md)
- [2.3.3 输出反馈控制](./02_Linear_Control/11_Output_Feedback_Control.md)
- [2.3.4 极点配置](./02_Linear_Control/12_Pole_Placement.md)

## 3. 非线性控制 (03_Nonlinear_Control)

### 3.1 非线性系统理论
- [3.1.1 非线性系统基础](./03_Nonlinear_Control/01_Nonlinear_System_Basics.md)
- [3.1.2 非线性系统分析](./03_Nonlinear_Control/02_Nonlinear_System_Analysis.md)
- [3.1.3 相平面分析](./03_Nonlinear_Control/03_Phase_Plane_Analysis.md)
- [3.1.4 描述函数法](./03_Nonlinear_Control/04_Describing_Function_Method.md)

### 3.2 非线性控制方法
- [3.2.1 反馈线性化](./03_Nonlinear_Control/05_Feedback_Linearization.md)
- [3.2.2 滑模控制](./03_Nonlinear_Control/06_Sliding_Mode_Control.md)
- [3.2.3 反步法](./03_Nonlinear_Control/07_Backstepping_Method.md)
- [3.2.4 李雅普诺夫方法](./03_Nonlinear_Control/08_Lyapunov_Method.md)

### 3.3 非线性稳定性
- [3.3.1 李雅普诺夫稳定性](./03_Nonlinear_Control/09_Lyapunov_Stability.md)
- [3.3.2 输入输出稳定性](./03_Nonlinear_Control/10_Input_Output_Stability.md)
- [3.3.3 绝对稳定性](./03_Nonlinear_Control/11_Absolute_Stability.md)
- [3.3.4 有限时间稳定性](./03_Nonlinear_Control/12_Finite_Time_Stability.md)

## 4. 最优控制 (04_Optimal_Control)

### 4.1 最优控制基础
- [4.1.1 最优控制问题](./04_Optimal_Control/01_Optimal_Control_Problem.md)
- [4.1.2 变分法](./04_Optimal_Control/02_Calculus_of_Variations.md)
- [4.1.3 最大值原理](./04_Optimal_Control/03_Maximum_Principle.md)
- [4.1.4 动态规划](./04_Optimal_Control/04_Dynamic_Programming.md)

### 4.2 线性二次型控制
- [4.2.1 线性二次型问题](./04_Optimal_Control/05_Linear_Quadratic_Problem.md)
- [4.2.2 代数黎卡提方程](./04_Optimal_Control/06_Algebraic_Riccati_Equation.md)
- [4.2.3 最优状态反馈](./04_Optimal_Control/07_Optimal_State_Feedback.md)
- [4.2.4 最优输出反馈](./04_Optimal_Control/08_Optimal_Output_Feedback.md)

### 4.3 随机最优控制
- [4.3.1 随机系统](./04_Optimal_Control/09_Stochastic_Systems.md)
- [4.3.2 随机最优控制](./04_Optimal_Control/10_Stochastic_Optimal_Control.md)
- [4.3.3 滤波理论](./04_Optimal_Control/11_Filtering_Theory.md)
- [4.3.4 卡尔曼滤波](./04_Optimal_Control/12_Kalman_Filter.md)

## 5. 鲁棒控制 (05_Robust_Control)

### 5.1 鲁棒性基础
- [5.1.1 鲁棒性概念](./05_Robust_Control/01_Robustness_Concepts.md)
- [5.1.2 不确定性建模](./05_Robust_Control/02_Uncertainty_Modeling.md)
- [5.1.3 鲁棒稳定性](./05_Robust_Control/03_Robust_Stability.md)
- [5.1.4 鲁棒性能](./05_Robust_Control/04_Robust_Performance.md)

### 5.2 H∞控制
- [5.2.1 H∞控制基础](./05_Robust_Control/05_H_Infinity_Control_Basics.md)
- [5.2.2 H∞标准问题](./05_Robust_Control/06_H_Infinity_Standard_Problem.md)
- [5.2.3 H∞控制器设计](./05_Robust_Control/07_H_Infinity_Controller_Design.md)
- [5.2.4 μ综合](./05_Robust_Control/08_Mu_Synthesis.md)

### 5.3 鲁棒控制方法
- [5.3.1 定量反馈理论](./05_Robust_Control/09_Quantitative_Feedback_Theory.md)
- [5.3.2 结构奇异值](./05_Robust_Control/10_Structured_Singular_Value.md)
- [5.3.3 线性矩阵不等式](./05_Robust_Control/11_Linear_Matrix_Inequalities.md)
- [5.3.4 鲁棒控制应用](./05_Robust_Control/12_Robust_Control_Applications.md)

## 6. 自适应控制 (06_Adaptive_Control)

### 6.1 自适应控制基础
- [6.1.1 自适应控制概念](./06_Adaptive_Control/01_Adaptive_Control_Concepts.md)
- [6.1.2 自适应控制结构](./06_Adaptive_Control/02_Adaptive_Control_Structure.md)
- [6.1.3 参数估计](./06_Adaptive_Control/03_Parameter_Estimation.md)
- [6.1.4 自适应律设计](./06_Adaptive_Control/04_Adaptation_Law_Design.md)

### 6.2 模型参考自适应控制
- [6.2.1 MRAC基础](./06_Adaptive_Control/05_MRAC_Basics.md)
- [6.2.2 直接MRAC](./06_Adaptive_Control/06_Direct_MRAC.md)
- [6.2.3 间接MRAC](./06_Adaptive_Control/07_Indirect_MRAC.md)
- [6.2.4 MRAC稳定性](./06_Adaptive_Control/08_MRAC_Stability.md)

### 6.3 自校正控制
- [6.3.1 自校正控制基础](./06_Adaptive_Control/09_Self_Tuning_Control_Basics.md)
- [6.3.2 最小方差控制](./06_Adaptive_Control/10_Minimum_Variance_Control.md)
- [6.3.3 广义最小方差控制](./06_Adaptive_Control/11_Generalized_Minimum_Variance_Control.md)
- [6.3.4 自校正控制应用](./06_Adaptive_Control/12_Self_Tuning_Control_Applications.md)

## 7. 智能控制 (07_Intelligent_Control)

### 7.1 模糊控制
- [7.1.1 模糊控制基础](./07_Intelligent_Control/01_Fuzzy_Control_Basics.md)
- [7.1.2 模糊推理](./07_Intelligent_Control/02_Fuzzy_Reasoning.md)
- [7.1.3 模糊控制器设计](./07_Intelligent_Control/03_Fuzzy_Controller_Design.md)
- [7.1.4 模糊控制应用](./07_Intelligent_Control/04_Fuzzy_Control_Applications.md)

### 7.2 神经网络控制
- [7.2.1 神经网络基础](./07_Intelligent_Control/05_Neural_Network_Basics.md)
- [7.2.2 神经网络控制器](./07_Intelligent_Control/06_Neural_Network_Controllers.md)
- [7.2.3 神经网络学习](./07_Intelligent_Control/07_Neural_Network_Learning.md)
- [7.2.4 神经网络控制应用](./07_Intelligent_Control/08_Neural_Network_Control_Applications.md)

### 7.3 其他智能控制
- [7.3.1 遗传算法控制](./07_Intelligent_Control/09_Genetic_Algorithm_Control.md)
- [7.3.2 粒子群优化控制](./07_Intelligent_Control/10_Particle_Swarm_Optimization_Control.md)
- [7.3.3 专家系统控制](./07_Intelligent_Control/11_Expert_System_Control.md)
- [7.3.4 混合智能控制](./07_Intelligent_Control/12_Hybrid_Intelligent_Control.md)

## 8. 分布式控制 (08_Distributed_Control)

### 8.1 分布式系统基础
- [8.1.1 分布式控制概念](./08_Distributed_Control/01_Distributed_Control_Concepts.md)
- [8.1.2 多智能体系统](./08_Distributed_Control/02_Multi_Agent_Systems.md)
- [8.1.3 分布式算法](./08_Distributed_Control/03_Distributed_Algorithms.md)
- [8.1.4 分布式稳定性](./08_Distributed_Control/04_Distributed_Stability.md)

### 8.2 一致性控制
- [8.2.1 一致性基础](./08_Distributed_Control/05_Consensus_Basics.md)
- [8.2.2 线性一致性](./08_Distributed_Control/06_Linear_Consensus.md)
- [8.2.3 非线性一致性](./08_Distributed_Control/07_Nonlinear_Consensus.md)
- [8.2.4 一致性应用](./08_Distributed_Control/08_Consensus_Applications.md)

### 8.3 编队控制
- [8.3.1 编队控制基础](./08_Distributed_Control/09_Formation_Control_Basics.md)
- [8.3.2 编队稳定性](./08_Distributed_Control/10_Formation_Stability.md)
- [8.3.3 编队变换](./08_Distributed_Control/11_Formation_Transformation.md)
- [8.3.4 编队控制应用](./08_Distributed_Control/12_Formation_Control_Applications.md)

## 9. 网络控制 (09_Networked_Control)

### 9.1 网络控制系统
- [9.1.1 网络控制概念](./09_Networked_Control/01_Networked_Control_Concepts.md)
- [9.1.2 网络诱导时延](./09_Networked_Control/02_Network_Induced_Delay.md)
- [9.1.3 数据包丢失](./09_Networked_Control/03_Packet_Loss.md)
- [9.1.4 网络拥塞](./09_Networked_Control/04_Network_Congestion.md)

### 9.2 网络控制方法
- [9.2.1 事件触发控制](./09_Networked_Control/05_Event_Triggered_Control.md)
- [9.2.2 采样控制](./09_Networked_Control/06_Sampled_Data_Control.md)
- [9.2.3 预测控制](./09_Networked_Control/07_Predictive_Control.md)
- [9.2.4 网络控制应用](./09_Networked_Control/08_Networked_Control_Applications.md)

### 9.3 网络安全控制
- [9.3.1 网络安全威胁](./09_Networked_Control/09_Network_Security_Threats.md)
- [9.3.2 安全控制策略](./09_Networked_Control/10_Security_Control_Strategies.md)
- [9.3.3 容错控制](./09_Networked_Control/11_Fault_Tolerant_Control.md)
- [9.3.4 安全控制应用](./09_Networked_Control/12_Security_Control_Applications.md)

## 10. 量子控制 (10_Quantum_Control)

### 10.1 量子系统基础
- [10.1.1 量子控制概念](./10_Quantum_Control/01_Quantum_Control_Concepts.md)
- [10.1.2 量子系统建模](./10_Quantum_Control/02_Quantum_System_Modeling.md)
- [10.1.3 量子态演化](./10_Quantum_Control/03_Quantum_State_Evolution.md)
- [10.1.4 量子测量](./10_Quantum_Control/04_Quantum_Measurement.md)

### 10.2 量子控制方法
- [10.2.1 量子最优控制](./10_Quantum_Control/05_Quantum_Optimal_Control.md)
- [10.2.2 量子反馈控制](./10_Quantum_Control/06_Quantum_Feedback_Control.md)
- [10.2.3 量子鲁棒控制](./10_Quantum_Control/07_Quantum_Robust_Control.md)
- [10.2.4 量子自适应控制](./10_Quantum_Control/08_Quantum_Adaptive_Control.md)

### 10.3 量子控制应用
- [10.3.1 量子计算控制](./10_Quantum_Control/09_Quantum_Computing_Control.md)
- [10.3.2 量子通信控制](./10_Quantum_Control/10_Quantum_Communication_Control.md)
- [10.3.3 量子传感控制](./10_Quantum_Control/11_Quantum_Sensing_Control.md)
- [10.3.4 量子控制应用](./10_Quantum_Control/12_Quantum_Control_Applications.md)

## 11. 综合理论 (11_Synthesis)

### 11.1 理论综合
- [11.1.1 控制理论统一](./11_Synthesis/01_Control_Theory_Unification.md)
- [11.1.2 控制方法综合](./11_Synthesis/02_Control_Method_Synthesis.md)
- [11.1.3 控制系统设计](./11_Synthesis/03_Control_System_Design.md)
- [11.1.4 控制性能分析](./11_Synthesis/04_Control_Performance_Analysis.md)

### 11.2 应用综合
- [11.2.1 工业控制应用](./11_Synthesis/05_Industrial_Control_Applications.md)
- [11.2.2 机器人控制应用](./11_Synthesis/06_Robotics_Control_Applications.md)
- [11.2.3 航空航天控制](./11_Synthesis/07_Aerospace_Control.md)
- [11.2.4 生物医学控制](./11_Synthesis/08_Biomedical_Control.md)

## 导航链接

- [返回主索引](../00_Master_Index/README.md)
- [哲学基础理论](../01_Philosophical_Foundation/README.md)
- [数学基础理论](../02_Mathematical_Foundation/README.md)
- [形式语言理论](../03_Formal_Language_Theory/README.md)
- [类型理论](../04_Type_Theory/README.md)

## 构建状态

- [x] 目录结构建立
- [ ] 基本概念内容
- [ ] 线性控制内容
- [ ] 非线性控制内容
- [ ] 最优控制内容
- [ ] 鲁棒控制内容
- [ ] 自适应控制内容
- [ ] 智能控制内容
- [ ] 分布式控制内容
- [ ] 网络控制内容
- [ ] 量子控制内容
- [ ] 综合理论内容

## 更新日志

- 2024-12-20: 创建控制理论目录结构
- 2024-12-20: 建立完整的树形导航体系
