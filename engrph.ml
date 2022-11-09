#use "topfind" ;;
#require "graphics" ;;
Graphics.open_graph "640x400";;
Graphics.clear_graph ();;

(* Take Pi(i), strings and return the scheme *)


let tm t=
  let m=ref t.(1) and n=(Array.length t -1) in begin
    for i=2 to n do
      if t.(i) > !m then m := t.(i);
    done;
    !m;
  end;;

let localise (a,b) t= (*To quickly place strand points on the screen *)
  let m=tm t in (100*a,40 + (20*m*(t.(a)-b)/(t.(a) - 1)));;

let nL = ref 0;;
let listL = ref [];;

let compt ()=
  incr nL;
  !nL;;

let rec fleche l (a,b) t=
  let flech = ref false in
  match l with
    [] -> ()
  |(m,n,p)::q -> begin
      Graphics.moveto a b;
      if 100*m <> a then begin Graphics.set_color (Graphics.rgb 250 50 50); flech:=true; end;
      let (c,d)=(localise (m,n) t) in begin
        if !flech then begin
          Graphics.lineto c d;
          if a < 100*m then Graphics.fill_poly [|(c,d);(c-3,d+3);(c-3,d-3)|] 
          else Graphics.fill_poly [|(c,d);(c+3,d-3);(c+3,d+3)|];
          if (String.length p)< 5 then begin
            Graphics.set_color (Graphics.rgb 150 50 150); 
            Graphics.moveto ((a+c)/2-9) (2+(b+d)/2);
            Graphics.draw_string ("g");
            Graphics.rmoveto 0 5;
            Graphics.draw_string p;
          end else begin
            listL := p:: !listL;
            Graphics.set_color (Graphics.rgb 150 50 150); 
            Graphics.moveto ((a+c)/2 -5) (2+(b+d)/2);
            Graphics.draw_string ("L");
            Graphics.rmoveto 0 (-5);
            Graphics.draw_string (string_of_int(compt()));
          end;
          Graphics.moveto c d;
        end else Graphics.moveto c d;
      end;
      fleche q (c,d) t;
    end;;

let rec traite l t=
  match l with
    [] -> ()
  |(a,b,_)::q -> let (c,d) = (localise (a,b) t) in begin
      Graphics.moveto c d;
      fleche q (c,d) t;
    end;;

let rec graphique l t=
  match l with
    [] -> ()
  |p::q -> begin traite p t; graphique q t;end;;

let rec mp l t= (* (_,1) is a circle, the others are full *)
  match l with
    []  -> ()
  |(a,b,_)::q -> begin
      let (c,d)=localise (a,b) t in
      if b = 1 then Graphics.draw_circle c d 2; mp q t;
    end;;

let flechebleu t=
  let n=(Array.length t -1) in begin
    Graphics.set_color (Graphics.rgb 75 75 255);
    for i=1 to n do
      let a=ref(localise (i,1) t) and b=ref(localise (i,1) t) in begin
        Graphics.moveto (fst !a) (snd !a);
        for j=2 to t.(i) do
          a:= !b;
          b:=localise (i,j) t;
          Graphics.moveto (fst(!a)-1) (snd !a);
          Graphics.lineto (fst(!b)-1) (snd !b);
          Graphics.moveto (fst(!a)+1) (snd !a);
          Graphics.lineto (fst(!b)+1) (snd !b);
          Graphics.fill_poly [|(fst !b,snd !b);(fst(!b)-3,snd(!b)+3);(fst(!b)+3,snd(!b)+3)|] ;
        done;
      end;
    done;
  end;;

let rec marque_point l t=
  match l with
    []  -> ()
  |p::q -> begin mp p t; marque_point q t; end;;

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

let transfo l=
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

let uselistL ()=
  let n=List.length !listL and s=(Graphics.size_x () - 200)in
  for i=1 to n do
    let h=List.hd !listL in begin
      listL:=List.tl (!listL);
      Graphics.moveto s (30+15*(i));
      Graphics.draw_string ("L");
      Graphics.rmoveto 0 (-5);
      Graphics.draw_string (string_of_int(n-i+1));
      Graphics.rmoveto 0 5;
      Graphics.draw_string (" = g");
      Graphics.rmoveto 0 5;
      Graphics.draw_string h;
    end;
  done;;

let graphl l=
  let t=transfo l  in begin
    Graphics.set_color (Graphics.black);
    marque_point l t;
    flechebleu t;
    graphique l t;
    Graphics.set_color (Graphics.black);
    for i=1 to (Array.length t - 1) do
      Graphics.moveto (100*i - 10) 25;
      Graphics.draw_string ("s");
      Graphics.rmoveto 0 (-5);
      Graphics.draw_string(string_of_int i);
    done; 
    uselistL ();
    t;
  end;;

(* graphl [[(1,2,"");(1,3,"R2,1")];[(2,1,"");(2,2,"R2,1");(3,2,"");(3,3,"K2,1")]];; *)