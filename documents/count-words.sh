INTR=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/introduction.tex | detex -l | tr -cd "0-9A-Za-z \n" | wc -w`
PREP=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/preparation.tex | detex -l | tr -cd "0-9A-Za-z \n" | wc -w`
IMPL=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/implementation.tex | detex -l | tr -cd "0-9A-Za-z \n" | wc -w`
EVAL=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/evaluation.tex | detex -l | tr -cd "0-9A-Za-z \n" | wc -w`
CONC=`sed -e 's/\$\+\([a-z_]\{3,\}\)/\1/g' chapters/conclusion.tex | detex -l | tr -cd "0-9A-Za-z \n" | wc -w`

echo "Introduction $INTR"
echo "Preparation $PREP"
echo "Implementation $IMPL"
echo "Evaluation $EVAL"
echo "Conclusion $CONC"

let "TOTAL = $INTR + $PREP + $IMPL + $EVAL + $CONC"

echo "Total $TOTAL"
