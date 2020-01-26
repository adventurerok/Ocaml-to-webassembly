
let my_count = ref 0;;

(* for loops are inclusive *)
for x = 1 to 100 do
  my_count := !my_count + x
done

let v_5050 = !my_count

let count2 = ref 0;;

for y = 100 downto 50 do
  count2 := !count2 + y
done

let v_3825 = !count2
