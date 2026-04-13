from pathlib import Path

# Fix 1: view/concept/理念分析与扩展分析/文件关联体系设计.md
fp1 = Path('view/concept/理念分析与扩展分析/文件关联体系设计.md')
content1 = fp1.read_text(encoding='utf-8')
content1 = content1.replace(
    '  - [02.1_经典确定性动力学.md](../02_动力学系统理论/02.1_经典确定性动力学.md) - 提供动力学基础\n'
    '  - [03.1_范畴论基础.md](../03_范畴论与形式化方法/03.1_范畴论基础.md) - 提供范畴论框架\n'
    '  - [07.1_Kubernetes动力学.md](../07_IT行业形式化应用/07.1_Kubernetes动力学.md) - 在容器编排中的应用\n'
    '  - [07.2_EKS系统分析.md](../07_IT行业形式化应用/07.2_EKS系统分析.md) - 在云原生系统中的应用',
    '  - 02.1_经典确定性动力学 - 提供动力学基础\n'
    '  - 03.1_范畴论基础 - 提供范畴论框架\n'
    '  - 07.1_Kubernetes动力学 - 在容器编排中的应用\n'
    '  - 07.2_EKS系统分析 - 在云原生系统中的应用'
)
content1 = content1.replace('[文档名](链接)', '[文档名](#)')
fp1.write_text(content1, encoding='utf-8')
print('Fixed', fp1)

# Fix 2: Concept/TuningCompute/02_技术实施指南与最佳实践.md
fp2 = Path('Concept/TuningCompute/02_技术实施指南与最佳实践.md')
content2 = fp2.read_text(encoding='utf-8')
content2 = content2.replace(
    '- 📖 [虚拟化容器化部署终极指南](../Deployment/01_虚拟化容器化部署终极指南.md)\n'
    '- 📖 [虚拟化部署指南](../Deployment/01_虚拟化部署/README.md)\n'
    '- 📖 [容器化部署指南](../Deployment/02_容器化部署/README.md)\n'
    '- 📖 [混合部署架构](../Deployment/03_混合部署架构/README.md)\n'
    '- 📖 [Container技术详解](../Container/README.md)\n'
    '- 📖 [vSphere VMware技术](../vShpere_VMware/README.md)\n'
    '- 📖 [Security安全指南](../Security/README.md)\n'
    '- 📖 [Semantic形式化验证](../Semantic/README.md)',
    '- 📖 虚拟化容器化部署终极指南\n'
    '- 📖 虚拟化部署指南\n'
    '- 📖 容器化部署指南\n'
    '- 📖 混合部署架构\n'
    '- 📖 Container技术详解\n'
    '- 📖 vSphere VMware技术\n'
    '- 📖 Security安全指南\n'
    '- 📖 Semantic形式化验证'
)
fp2.write_text(content2, encoding='utf-8')
print('Fixed', fp2)
