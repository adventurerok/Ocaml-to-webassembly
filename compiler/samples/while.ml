
let my_ref = ref 0;;
let my_count = ref 0;;

while (!my_ref) < 10 do
  my_count := !my_count + !my_ref;
  my_ref := !my_ref + 1
done

let v_10 = !my_ref;;

let v_45 = !my_count;;
