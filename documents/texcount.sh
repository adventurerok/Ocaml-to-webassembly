INTR=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/introduction.tex | texcount -`
PREP=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/preparation.tex | texcount -`
IMPL=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/implementation.tex | texcount -`
EVAL=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/evaluation.tex | texcount -`
CONC=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/conclusion.tex | texcount -`

echo "Introduction $INTR"
echo "Preparation $PREP"
echo "Implementation $IMPL"
echo "Evaluation $EVAL"
echo "Conclusion $CONC"

let "TOTAL = $INTR + $PREP + $IMPL + $EVAL + $CONC"

echo "Total $TOTAL"
