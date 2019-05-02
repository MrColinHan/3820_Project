module Test

open Absyn
//open System.Collections.Generic
//open System.Windows.Forms.VisualStyles.VisualStyleElement.Menu

let cases =
  (
    let s = "0"
    let e = ConI 0
    (s, e)) ::
  (
    let s = "5+3*4"
    let e = Prim2 ("+",ConI 5,Prim2 ("*",ConI 3,ConI 4))
    (s, e)) ::
  (
   let s = "-3 < 4"
   let e = Prim2 ("<",Prim1 ("-",ConI 3),ConI 4)
   (s, e)) ::
  (
    let s = "!(3 = 4)"
    let e = Prim1 ("!",Prim2 ("=",ConI 3,ConI 4))
    (s, e)) ::
  (
    let s = "3+1 = 4 && 4 <= 3"
    let e = Prim2 ("&&",Prim2 ("=",Prim2 ("+",ConI 3,ConI 1),ConI 4), Prim2 ("<=",ConI 4,ConI 3))
    (s, e)) ::
  (
    let s = "if 3 = 2 then 0 else 1 + 4"
    let e = If (Prim2 ("=",ConI 3,ConI 2),ConI 0,Prim2 ("+",ConI 1,ConI 4))
    (s, e)) ::
  (
    let s = "3 + if 3 = 2 then 0 else 1"
    let e = Prim2 ("+",ConI 3,If (Prim2 ("=",ConI 3,ConI 2),ConI 0,ConI 1))
    (s, e)) ::
  (
    let s = "match x with | 0 -> 1 | _ -> -1 end"
    let e = Match (Var "x",[(Some (ConI 0), ConI 1); (None, Prim1 ("-",ConI 1))])
    (s, e)) ::
  (
    let s = "4; true"
    let e = Prim2 (";",ConI 4,ConB true)
    (s, e)) ::
  (
    let s = "4 * (true; 6)"
    let e = Prim2 ("*",ConI 4,Prim2 (";",ConB true,ConI 6))
    (s, e)) ::
  (
    let s = "( )"
    let e = List []
    (s, e)) ::
  (
    let s = "(1,false,())"
    let e = List [ConI 1; ConB false; List []]
    (s, e)) ::
  (
    let s = "(1,(2,3),4)"
    let e = List [ConI 1; List [ConI 2; ConI 3]; ConI 4]
    (s, e)) ::
  (
    let s = "(true,false)[1]"
    let e = Item (1, List [ConB true; ConB false])
    (s, e)) ::
  (
    let s = "((5,6),false)[1][2]"
    let e = Item (2, Item (1, List [List [ConI 5; ConI 6]; ConB false]))
    (s, e)) ::
  (
    let s = "1 + {3}"
    let e = Prim2 ("+",ConI 1,ConI 3)
    (s, e)) ::
  (
    let s = "print false"
    let e = Prim1 ("print",ConB false)
    (s, e)) ::
  (
    let s = "print (1 - 3)"
    let e = Prim1 ("print",Prim2 ("-",ConI 1,ConI 3))
    (s, e)) ::
  (
    let s = "([Int] [])"
    let e = ESeq (SeqT IntT)
    (s, e)) ::
  (
    let s = "([Int] [])"
    let e = ESeq (SeqT IntT)
    (s, e)) ::
  (
    let s = "([Bool] [])"
    let e = ESeq (SeqT BoolT)
    (s, e)) ::
  (
    let s = "([Nil] [])"
    let e = ESeq (SeqT (ListT []))
    (s, e)) ::
  (
    let s = "([[Int]] [])"
    let e = ESeq (SeqT (SeqT IntT))
    (s, e)) ::
  (
    let s = "([Int -> Nil] [])"
    let e = ESeq (SeqT (FunT (IntT, ListT [])))
    (s, e)) ::
  (
    let s = "
    ([[Int -> Int -> Bool]] [])"
    let e = ESeq (SeqT (SeqT (FunT (IntT, FunT (IntT,BoolT)))))
    (s, e)) ::
  (
    let s = "([(Nil, Int, Bool)] [])"
    let e = ESeq (SeqT (ListT [ListT []; IntT; BoolT]))
    (s, e)) ::
  (
    let s = "1 :: ([Int] [])"
    let e = Prim2 ("::",ConI 1,ESeq (SeqT IntT))
    (s, e)) ::
  (
    let s = "1 :: 2 :: ([Int] [])"
    let e = Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,ESeq (SeqT IntT)))
    (s, e)) ::
  (
    let s = "(1,2) :: (3,4) :: ([(Int,Int)] [])"
    let e = Prim2 ("::",List [ConI 1; ConI 2], Prim2 ("::",List [ConI 3; ConI 4],ESeq (SeqT (ListT [IntT; IntT]))))
    (s, e)) ::
  (
    let s = "hd (1 :: 2 :: ([Int] []))"
    let e = Prim1 ("hd",Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,ESeq (SeqT IntT))))
    (s, e)) ::
  (
    let s = "tl (1 :: 2 :: ([Int] []))"
    let e = Prim1 ("tl",Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,ESeq (SeqT IntT))))
    (s, e)) ::
  (
    let s = "ise([Int] [])"
    let e = Prim1 ("ise",ESeq (SeqT IntT))
    (s, e)) ::
  (
    let s = "ise(true::([Bool] []))"
    let e = Prim1 ("ise",Prim2 ("::",ConB true,ESeq (SeqT BoolT)))
    (s, e)) ::
  (
    let s = "var x = 4; x+1"
    let e = Let ("x",ConI 4,Prim2 ("+",Var "x",ConI 1))
    (s, e)) ::
  (
    let s = "{var x = 4; x+1}"
    let e = Let ("x",ConI 4,Prim2 ("+",Var "x",ConI 1))
    (s, e)) ::
  (
    let s = "
    var x = 4;
    var y = 6;
    x + y"
    let e = Let ("x",ConI 4,Let ("y",ConI 6,Prim2 ("+",Var "x",Var "y")))
    (s, e)) ::
  (
    let s = "
    var x = 4;
    print x;
    {var y = 6;
     print y
    }"
    let e = Let ("x",ConI 4,Prim2 (";",Prim1 ("print",Var "x"),Let ("y",ConI 6,Prim1 ("print",Var "y"))))
    (s, e)) ::
  (
    let s = "1 + {var tmp = 9; x + x}"
    let e = Prim2 ("+",ConI 1,Let ("tmp",ConI 9,Prim2 ("+",Var "x",Var "x")))
    (s, e)) ::
  (
    let s = "
    var a = (3,4);
    a[1] < a[2]
    "
    let e = Let ("a",List [ConI 3; ConI 4],Prim2 ("<",Item (1, Var "a"),Item (2, Var "a")))
    (s, e)) ::
  (
    let s = "
    var e = ([Bool] []);
    true::false::e
    "
    let e = Let ("e",ESeq (SeqT BoolT),Prim2 ("::",ConB true,Prim2 ("::",ConB false,Var "e")))
    (s, e)) ::
  (
    let s = "fn (Int x) => x end"
    let e = Anon (IntT, "x", Var "x")
    (s, e)) ::
  (
    let s = "var f = fn (Int x) => x end; f"
    let e = Let ("f",Anon (IntT,"x",Var "x"),Var "f")
    (s, e)) ::
  (
    let s = "var f = fn (Int x) => x end; f"
    let e = Let ("f",Anon (IntT, "x",Var "x"),Var "f")
    (s, e)) ::
  (
    let s = "var f = fn (Int x) => x end; f(10)"
    let e = Let ("f",Anon (IntT,"x",Var "x"),Call (Var "f",ConI 10))
    (s, e)) ::
  (
    let s = "fun f (Int x) = x; f"
    let e = Let ("f",Anon (IntT, "x",Var "x"),Var "f")
    (s, e)) ::
  (
    let s = "fun f (Int x) = {fun g(Int y) = x+y; g}; f(3)(4)"
    let e = Let ("f", Anon (IntT, "x",Let ("g",Anon (IntT,"y",Prim2 ("+",Var "x",Var "y")),Var "g")),Call (Call (Var "f",ConI 3),ConI 4))
    (s, e)) ::
  (
    let s = "fun f (Int x) = fn (Int y) => x+y end; f(3)(4)"
    let e = Let ("f",Anon (IntT,"x",Anon (IntT,"y",Prim2 ("+",Var "x",Var "y"))), Call (Call (Var "f",ConI 3),ConI 4))
    (s, e)) ::
  (
    let s = "
    fun f (Int -> Bool g) = if g(1) then 10 else 11;
    fun h (Int x) = 0 < x;
    f(h)
    "
    let e = Let ("f",Anon (FunT (IntT,BoolT), "g",If (Call (Var "g",ConI 1),ConI 10,ConI 11)), Let ("h",Anon (IntT,"x",Prim2 ("<",ConI 0,Var "x")),Call (Var "f",Var "h")))
    (s, e)) ::
  (
    let s = "fun rec f (Int x) : Int = if x <= 0 then 1 else x + f(x-1); f(5)"
    let e = Letrec ("f",IntT,"x", IntT, If (Prim2 ("<=",Var "x",ConI 0),ConI 1, Prim2 ("+",Var "x",Call (Var "f",Prim2 ("-",Var "x",ConI 1)))), Call (Var "f",ConI 5))
    (s, e)) ::
  (
    let s = "
    fun rec pr(Int x): Nil =
      if x <= 0 then
        print(0)
      else {
        print(x);
        pr(x-1)
      };
    pr(5)"
    let e = Letrec ("pr",IntT,"x", ListT [], If (Prim2 ("<=",Var "x",ConI 0),Prim1 ("print",ConI 0), Prim2 (";",Prim1 ("print",Var "x"),Call (Var "pr",Prim2 ("-",Var "x",ConI 1)))),Call (Var "pr",ConI 5))
    (s, e)) ::
  (
    let s = "
    fun rec len([Int] l): Int = if ise(l) then 0 else 1 + len(tl(l));
    len(1::2::([Int] []))"
    let e = Letrec ("len",SeqT IntT,"l", IntT, If (Prim1 ("ise",Var "l"),ConI 0, Prim2 ("+",ConI 1,Call (Var "len",Prim1 ("tl",Var "l")))), Call (Var "len",Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,ESeq (SeqT IntT)))))
    (s, e)) ::
  (
    let s = "fn (Int x, Int y) => x - y end"
    let e = Anon (ListT [IntT; IntT], "$list", Let ("x",Item (1, Var "$list"), Let ("y",Item (2, Var "$list"),Prim2 ("-",Var "x",Var "y"))))
    (s, e)) ::
  (
    let s = "fun f(Int x, Int y) = x - y; f(5,4)"
    let e = Let ("f", Anon (ListT [IntT; IntT], "$list", Let ("x",Item (1, Var "$list"), Let ("y",Item (2, Var "$list"),Prim2 ("-",Var "x",Var "y")))), Call (Var "f",List [ConI 5; ConI 4]))
    (s, e)) ::
  (
    let s = "
    var p = (1,3);
    fun f(Int x, Int y) = x - y;
    f(p)"
    let e = Let ("p",List [ConI 1; ConI 3], Let ("f", Anon (ListT [IntT; IntT], "$list", Let ("x",Item (1, Var "$list"), Let ("y",Item (2, Var "$list"),Prim2 ("-",Var "x",Var "y")))), Call (Var "f",Var "p")))
    (s, e)) ::
  (
    let s = "fun f(Int x, Int y, Int z) = x - y * z ; f(5,4,2)"
    let e = Let ("f", Anon (ListT [IntT; IntT; IntT], "$list", Let ("x",Item (1, Var "$list"), Let ("y",Item (2, Var "$list"), Let ("z",Item (3, Var "$list"), Prim2 ("-",Var "x",Prim2 ("*",Var "y",Var "z")))))), Call (Var "f",List [ConI 5; ConI 4; ConI 2]))
    (s, e)) ::
  (
    let s = "
    fun rec mem(Int x, [Int] l): Bool =
      if ise(l) then false
      else if x = hd(l) then true else mem(x, tl(l));
    mem(2, 1::2::([Int] []))"
    let e = Letrec ("mem",ListT [IntT; SeqT IntT], "$list", BoolT, Let ("x",Item (1, Var "$list"), Let ("l",Item (2, Var "$list"),If (Prim1 ("ise",Var "l"),ConB false,If (Prim2 ("=",Var "x",Prim1 ("hd",Var "l")),ConB true, Call (Var "mem",List [Var "x"; Prim1 ("tl",Var "l")]))))),Call (Var "mem", List [ConI 2; Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,ESeq (SeqT IntT)))]))
    (s, e)
  ) ::
  (
    let s = "
    fun inc (Int x) = x + 1;
    fun add (Int x, Int y) = x + y;
    fun cadd (Int x) = fn (Int y) => x + y end;
    var y = add(3, inc(4));
    var x = cadd(3)(7-y);
    var z = x * 3;
    fun rec fac (Int n) : Int =
      match n with
      | 0 -> 1
      | 1 -> 1
      | _ -> n * fac(n - 1)
      end
    ;
    print x; print y;
    x :: y :: z :: fac(z) :: ([Int] [])"
    let e = Let("inc",Anon (IntT,"x",Prim2 ("+",Var "x",ConI 1)), Let ("add",Anon(ListT [IntT; IntT],"$list", Let ("x",Item (1,Var "$list"),Let ("y",Item (2,Var "$list"),Prim2 ("+",Var "x",Var "y")))),Let("cadd",Anon (IntT,"x",Anon (IntT,"y",Prim2 ("+",Var "x",Var "y"))), Let ("y",Call (Var "add",List [ConI 3; Call (Var "inc",ConI 4)]),Let("x", Call (Call (Var "cadd",ConI 3),Prim2 ("-",ConI 7,Var "y")), Let ("z",Prim2 ("*",Var "x",ConI 3),Letrec("fac",IntT,"n",IntT, Match (Var "n",[(Some (ConI 0), ConI 1); (Some (ConI 1), ConI 1); (None,Prim2("*",Var "n", Call (Var "fac",Prim2 ("-",Var "n",ConI 1))))]), Prim2 (";",Prim1 ("print",Var "x"),Prim2(";",Prim1 ("print",Var "y"), Prim2 ("::",Var "x",Prim2("::",Var "y", Prim2 ("::",Var "z",Prim2("::",Call (Var "fac",Var "z"), ESeq (SeqT IntT))))))))))))))
    (s, e))::
  (
    let s = "
    fun f(Int x, Bool b) =
      match b with
      | true -> {x + 1}
      | _    -> x
      end
    ;
    f(3,true)"
    let e = Let("f", Anon (ListT [IntT; BoolT],"$list",Let("x",Item (1,Var "$list"), Let ("b",Item (2,Var "$list"),Match(Var "b", [(Some (ConB true), Prim2 ("+",Var "x",ConI 1));(None, Var "x")])))),Call (Var "f",List [ConI 3; ConB true]))
    (s, e)) ::
  (
    let s = "
    var E = ([Int] []);
    fun reverse ([Int] l) = {
      fun rec rev ([Int] l1, [Int] l2): [Int] =
        if ise(l1) then
          l2
        else
          rev(tl(l1), hd(l1)::l2);
      rev(l, E)
    };
    reverse (1::2::3::E)"
    let e = Let ("E",ESeq (SeqT IntT),Let ("reverse",Anon (SeqT IntT, "l",Letrec ("rev", ListT [SeqT IntT; SeqT IntT],"$list", SeqT IntT, Let ("l1",Item (1, Var "$list"),Let ("l2",Item (2, Var "$list"), If (Prim1 ("ise",Var "l1"),Var "l2",Call (Var "rev",List [Prim1 ("tl",Var "l1");Prim2 ("::",Prim1 ("hd",Var "l1"),Var "l2")])))),Call (Var "rev",List [Var "l"; Var "E"]))),Call (Var "reverse",Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,Prim2 ("::",ConI 3,Var "E"))))))
    (s, e))::
  (
    let s = "
    var E = ([Int] []);
    fun reverse ([Int] s) = {
      fun rec rev ([Int] s1, [Int] s2): [Int] =
        match s1 with
        | E -> s2
        | _ -> {
                 var h = hd(s1);
                 var t = tl(s1);
                 rev(t, h::s2)
               }
        end
      ;
      rev(s, E)
    };
    reverse (1::2::3::E)"
    let e = Let("E",ESeq (SeqT IntT), Let ("reverse",Anon(SeqT IntT,"s",Letrec("rev",ListT [SeqT IntT; SeqT IntT],"$list",SeqT IntT, Let ("s1",Item (1,Var "$list"),Let("s2",Item (2,Var "$list"), Match (Var "s1",[(Some (Var "E"), Var "s2"); (None,Let("h",Prim1 ("hd",Var "s1"), Let ("t",Prim1 ("tl",Var "s1"),Call(Var "rev", List [Var "t"; Prim2 ("::",Var "h",Var "s2")]))))]))), Call (Var "rev",List [Var "s"; Var "E"]))),Call (Var "reverse", Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,Prim2 ("::",ConI 3,Var "E"))))))
    (s, e)) ::
  [ (
    let s = "
    fun rec map ((Int -> Int) f) : ([Int] -> [Int]) =
      fn ([Int] l) =>
        if ise(l) then l else f(hd(l)) :: map(f)(tl(l))
      end ;
    map (fn (Int x) => 2*x end) (10::20::30::([Int] []))"
    let e = Letrec ("map",FunT (IntT,IntT), "f", FunT (SeqT IntT,SeqT IntT), Anon(SeqT IntT, "l",If(Prim1 ("ise",Var "l"),Var "l",Prim2("::",Call (Var "f",Prim1 ("hd",Var "l")),Call (Call (Var "map",Var "f"),Prim1 ("tl",Var "l"))))),Call(Call (Var "map",Anon (IntT, "x",Prim2 ("*",ConI 2,Var "x"))),Prim2 ("::",ConI 10,Prim2 ("::",ConI 20,Prim2 ("::",ConI 30,ESeq (SeqT IntT))))))
    (s, e)) ]
