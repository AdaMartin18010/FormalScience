#!/bin/bash
# 批量为所有视角目录添加TOC的脚本

echo "========================================="
echo "批量TOC生成 - 全部视角"
echo "========================================="

# P0: 主Index文档（3个）
echo ""
echo "[P0] 处理主Index文档..."
uv run add_toc_batch.py AI_model_Perspective --output TOC_REPORT_AI_P0.md
uv run add_toc_batch.py FormalLanguage_Perspective --output TOC_REPORT_Formal_P0.md
uv run add_toc_batch.py Information_Theory_Perspective --output TOC_REPORT_Info_P0.md

echo ""
echo "========================================="
echo "全部完成！"
echo "========================================="
echo ""
echo "生成的报告："
echo "- TOC_REPORT_AI_P0.md"
echo "- TOC_REPORT_Formal_P0.md"
echo "- TOC_REPORT_Info_P0.md"
echo ""
echo "请检查报告，确认无误后可继续处理其他文档"

