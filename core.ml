(*#use "engrph.ml";;*)  (* Use this to have an ugly visualisation of the protocol you wrote if the attack seems odd *)
#use "nogrph.ml";; (* fast mode without intermediate visual*)
#use "lect.ml";;
#use "attack.ml";;
#use "test3.ml";;

let filename=Sys.argv.(1);;

let rec insere p l lp=
  match l with
    [] -> [p]
  |t::q -> if (fst3(List.hd(List.rev t))<lp) then t::(insere p q lp) else p::l;;

let rec order l ll=
  match l with
    [] -> ll
  |p::q -> order q (insere p ll (fst3(List.hd(List.rev p))));;

let unit a= ();;

let attack_auto ()=
  let lpi=go (filename^".txt") in
  let t=graphl(lpi) in
  let nbpart=Array.length t -1 in
  let lpii = convpi(order lpi []) in
  unit(updl(lpii));
  if nbpart=2 then print_string("With overwhelming probably protocols with 2 users cannot be attacked \n\n")
  else if nbpart=3 then
    begin print_string("3 users detective, trying to find an attack, no promises here \n\n"); 
      let (aa,bb)=test3 lpii in
      if aa then begin print_string("An attack is possible, trying to find precisely how... \n");
        unit(attack3 t lpii);end else
      if bb then print_string("Max depth reach, time to take a nap \n\n")
      else print_string("This protocol can be provably shown not to be vulnerable to clique attacks \n\n");end
  else if nbpart=4 then begin print_string("4 users detected, attack in progress \n\n"); 
    unit(attack4 t lpii filename); end
  else begin print_string("More than 4 users detected, easy attack in progress \n\n"); 
    unit(attack5 t lpii filename); 
  end;
  print_string("Digest written in "^filename^".tex");;

attack_auto ();;