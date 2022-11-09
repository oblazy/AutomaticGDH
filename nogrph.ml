(* Take Pi(i), strings and return the scheme *)

let rec upd (a,b,c) ll=
  match ll with
    [] -> [(a,b)]
  |(t,v)::q -> if t<>a then (t,v)::upd (a,b,c) q else if b > v then (a,b)::q else ll;;  

let rec upd2 l ll=
  match l with
    [] -> ll
  |p::q -> upd2 q (upd p ll) ;;

let rec cherche_max l ll=
  match l with
    [] -> ll
  |p::q -> cherche_max q (upd2 p ll) ;;

let graphl l=
  let l1 = ref (cherche_max l []) in
  let t=Array.make (1+List.length !l1) 0 in begin
    while !l1<>[] do
      let (a,b)=List.hd(!l1) in begin
        l1 := List.tl(!l1);
        t.(a)<- b;
      end;
    done;
    t;
  end;;

(* graphl [[(1,2,"");(1,3,"R2,1")];[(2,1,"");(2,2,"R2,1");(3,2,"");(3,3,"K2,1")]];; *)