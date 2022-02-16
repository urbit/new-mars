|%
::  $coot: description of knowledge at a call site
::  $foot: annotated Nock tree with subject knowledge
::  $jute: a jet dashboard
::  $memo: analysis memoization, updated/inspected at eval boundaries
::  $sock: partial knowledge of a noun
::
+$  coot
  $%  ::  %dyn: don't know the formula;
      ::        generate a full eval: check cache or codegen,
      ::        guard on stored sock
      ::  %mis: know the formula, not memoized;
      ::        do a fresh inline codegen with a new label
      ::  %rec: a recursive call, memo table has a blackhole
      ::  %hit: a recognized call, memo table has an entry
      ::  %jet: jump to a statically known jet
      ::
      ::    %rec and %hit both mean we will generate jumps to labels;
      ::    they differ because for %rec the analysis must treat the call as
      ::    unknowable, while for %hit we do not re-analyze the call but return
      ::    the memoized sock
      ::
      [%dyn =sock]
      [%mis =foot]
      [%rec =sock f=*]
      [%hit res=sock]
      [%jet jet=@tas]  :: XX s/b path
  ==
::
+$  foot
  $:  $%  [%1 b=*]
          [%2 b=foot c=foot =coot]
          [%3 b=foot]
          [%4 b=foot]
          [%5 b=foot c=foot]
          [%6 b=foot c=(unit foot) d=(unit foot)]
          [%7 b=foot c=foot]
          [%8 b=foot c=foot]
          [%9 b=@ c=foot =coot]
          [%10 [b=@ c=foot] d=foot]
          [%11 b=@ c=foot]
          [%11 [b=@ c=foot] d=foot]
          [%12 ref=foot path=foot]
          [%cell p=foot q=foot]
          [%0 b=@]
        ==
    s=sock
    r=sock
  ==
::
+$  jute  (map * (list (pair sock (pair gate @tas))))
::
+$  memo  (map (pair sock *) (pair (unit sock) (unit @tas)))
::
+$  sock
  $%  [%know k=*]
      [%bets p=sock q=sock]
      [%gues ~]
  ==
--
::
|%
+|  %jet-opts
::
++  bord  *jute
::  Check for a jet
++  juke
  |=  [=jute s=sock f=*]
  =/  jets  ?~(j=(~(get by jute) f) ~ u.j)
  |-  ^-  (unit (pair gate @tas))
  ?~  jets
    ~
  ?:  (mous p.i.jets s)
    `q.i.jets
  $(jets t.jets)
::
+|  %sock-opts
::
::  +mous: test whether a sock nests in another sock
::
::    a=sock nests in b=sock if b has the same information as a, or
::    strictly more information
::
++  mous
  |=  [a=sock b=sock]
  ^-  ?
  ?:  =(a b)  &
  ?-  -.a
    %gues  &
  ::
  ::  XX seems like this will only nest in the case of [b]
  ::  being an improperly non-normalized %bets ...
  ::
    %know  ?&  ?=([%bets ^] b)
               ?=(^ k.a)
               $(a [%know -.k.a], b p.b)
               $(a [%know +.k.a], b q.b)
           ==
  ::
    %bets  ?|  ?&  ?=([%know ^] b)
                   $(a p.a, b [%know -.k.b])
                   $(a q.a, b [%know +.k.b])
               ==
               ?&  ?=([%bets *] b)
                   $(a p.a, b p.b)
                   $(a q.a, b q.b)
  ==       ==  ==
::  learn a noun at an address
::
++  darn
  |=  [s=sock b=@ n=*]
  ?<  =(b 0)
  |-  ^-  sock
  ?:  =(b 1)
    [%know n]
  ?:  ?=([%know *] s)
    [%know .*([k.s n] [%10 [b [%0 3]] [%0 2]])]
  =+  [now lat]=[(cap b) (mas b)]
  %-  both
  ?-  -.s
    %gues  ?-  now
             %2  [$(b lat) s]
             %3  [s $(b lat)]
           ==
    %bets  ?-  now
             %2  [$(s p.s, b lat) q.s]
             %3  [p.s $(s q.s, b lat)]
  ==       ==
::  axis into a sock
::
++  yarn
  |=  [s=sock b=@]
  ?<  =(b 0)
  |-  ^-  sock
  ?:  =(b 1)  s
  ?-  -.s
    %know  [%know .*(k.s [%0 b])]
    %gues  s
    %bets  ?-  (cap b)
             %2  $(b (mas b), s p.s)
             %3  $(b (mas b), s q.s)
  ==       ==
::  cons two socks
::
++  both
  |=  [a=sock b=sock]
  ?:  &(?=(%know -.a) ?=(%know -.b))
    [%know k.a k.b]
  ::  XX is it worth preserving [%bets gues+~ gues+~]
  ::
  ?:  &(?=(%gues -.a) ?=(%gues -.b))
    a
  [%bets a b]
::  make a new sock from 2 socks (and an axis)
::
++  knit
  |=  [s=sock b=@ t=sock]
  ?<  =(b 0)
  |-  ^-  sock
  ?:  =(b 1)  t
  =+  [now lat]=[(cap b) (mas b)]
  %-  both
  ?-  -.s
    %know  ~|  %know-atom
           ?-  now
             %2  [$(s [%know -.k.s], b lat) [%know +.k.s]]
             %3  [[%know -.k.s] $(s [%know +.k.s], b lat)]
           ==
  ::
    %bets  ?-  now
             %2  [$(s p.s, b lat) q.s]
             %3  [p.s $(s q.s, b lat)]
           ==
  ::
    %gues  ?-  now
             %2  [$(b lat) s]
             %3  [s $(b lat)]
  ==       ==
::
++  pear
  |=  [a=sock b=sock]
  ^-  sock
  ?.  ?&  ?=([%know *] a)
          ?=([%know *] b)
      ==
    [%gues ~]
  [%know =(a b)]
::
++  deep
  |=  a=sock
  ?-  -.a
    %know  [%know .?(k.a)]
    %bets  [%know 0]
    %gues  a
  ==
::
++  cort
  |=  =coot
  ^-  sock
  ?-  -.coot
    %dyn  [%gues ~]
    %mis  r.foot.coot
    %rec  [%gues ~]
    %hit  res.coot
    %jet  [%gues ~]
  ==
::
+|  %analyses
::
::  Compute what we know of a Nock formula's result
++  wash
  =|  m=memo
  |=  [s=sock f=*]
  |-  ^-  [sock memo]
  =/  sockf
    |=  [s=sock f=sock] 
    ^-  [sock memo]
    ?.  ?=  [%know *]  f
      [[%gues ~] m]
    ?~  mem=(~(get by m) s k.f)
      :: memo miss
      =.  m  (~(put by m) [s k.f] [~ ~])
      =^  r  m  ^$(s s, f +.f)
      [r (~(put by m) [s k.f] [`r ~])]
    ?~  p.u.mem
      ::  memo blackhole
      [[%gues ~] m]
    ::  memo hit]
    [u.p.u.mem m]
  ?+  f  ~|(%wash-bonk !!)
      [[* *] *]
    =^  pres  m  $(f -.f)
    =^  qres  m  $(f +.f)
    [(both pres qres) m]
  ::
      [%0 b=@]
    [(yarn s b.f) m]
  ::
      [%1 b=*]
    [[%know b.f] m]
  ::
      [%2 b=* c=*]
    =^  bres  m  $(f b.f)
    =^  cres  m  $(f c.f)
    (sockf s=bres f=cres)
  ::
      [%3 b=*]
    =^  bres  m  $(f b.f)
    [(deep bres) m]
  ::
      [%4 b=*]
    =^  bres  m  $(f b.f)
    [[%gues ~] m]
  ::
      [%5 b=* c=*]
    =^  bres  m  $(f b.f)
    =^  cres  m  $(f c.f)
    [(pear bres cres) m]
  ::
      [%6 b=* c=* d=*]
    =^  bres  m  $(f b.f)
    ?+  bres  ~|(%wash-nest !!)
        [%know %0]
      $(f c.f)
    ::
        [%know %1]
      $(f d.f)
    :: can we merge them somehow in this case? things the branches
    :: agree on?
        [%gues ~]
      [[%gues ~] m]
    ==
  ::
      [%7 b=* c=*]
    =^  bres  m  $(f b.f)
    $(s bres, f c.f)
  ::
      [%8 b=* c=*]
    =^  bres  m  $(f b.f)
    $(s (both bres s), f c.f)
  ::
      [%9 b=@ c=*]
    =^  cres  m  $(f c.f)
    (sockf cres (yarn cres b.f))
  ::
      [%10 [b=@ c=*] d=*]
    =^  cres  m  $(f c.f)
    =^  dres  m  $(f d.f)
    [(knit dres b.f cres) m]
  ::
      [%11 b=@ c=*]
    $(f c.f)
  ::
      [%11 [b=@ c=*] d=*]
    =^  cres  m  $(f c.f)
    ?:  =(b.f %data)
      =/  c  c.f
      |-
      ?:  ?=  [[%0 @] *]  c
        =.  s  (knit s ->.c [%gues ~])
        $(c +.c)
      ^$(f d.f)
    $(f d.f)
  ::
      [%12 ref=* path=*]
    =^  rres  m  $(f ref.f)
    =^  pres  m  $(f path.f)
    [[%gues ~] m]
  ==
::
++  pull
  =|  m=memo
  |=  [=jute s=sock f=*]
  ^-  [foot memo]
  =/  labl  [s f]
  |^
  ^-  [foot memo]
  ?+  f
    ~|  "unrecognized nock {<f>}"
    ~|(%pull-bonk !!)
  ::
      [[* *] *]
    =^  pfoot  m  $(f -.f)
    =^  qfoot  m  $(f +.f)
    [[[%cell pfoot qfoot] s (both r.pfoot r.qfoot)] m]
  ::
      [%0 b=@]
    [[[%0 b.f] s=s r=(yarn s b.f)] m]
  ::
      [%1 b=*]
    [[[%1 b.f] s=s r=[%know b.f]] m]
  ::
      [%2 b=* c=*]
    =^  bfoot  m  $(f b.f)
    =^  cfoot  m  $(f c.f)
    =^  coot   m  (sockf r.bfoot r.cfoot)
    [[[%2 bfoot cfoot coot] s (cort coot)] m]
  ::
      [%3 b=*]
    =^  bfoot  m  $(f b.f)
    [[[%3 bfoot] s (deep r.bfoot)] m]
  ::
      [%4 b=*]
    =^  bfoot  m  $(f b.f)
    [[[%4 bfoot] s [%gues ~]] m]
  ::
      [%5 b=* c=*]
    =^  bfoot  m  $(f b.f)
    =^  cfoot  m  $(f c.f)
    [[[%5 bfoot cfoot] s (pear r.bfoot r.cfoot)] m]
  ::
      [%6 b=* c=* d=*]
    =^  bfoot  m  $(f b.f)
    ?+  r.bfoot  ~|(%pull-nest !!)
        [%know %0]
      =^  cfoot  m  $(f c.f)
      [[[%6 bfoot `cfoot ~] s r.cfoot] m]
    ::
        [%know %1]
      =^  dfoot  m  $(f d/f)
      [[[%6 bfoot ~ `dfoot] s r.dfoot] m]
    ::
        [%gues ~]
      =^  cfoot  m  $(f c.f)
      =^  dfoot  m  $(f d.f)
      [[[%6 bfoot `cfoot `dfoot] s [%gues ~]] m]
    ==
  ::
      [%7 b=* c=*]
    =^  bfoot  m  $(f b.f)
    =^  cfoot  m  $(s r.bfoot, f c.f)
    [[[%7 bfoot cfoot] s r.cfoot] m]
  ::
      [%8 b=* c=*]
    =^  bfoot  m  $(f b.f)
    =^  cfoot  m  $(s (both r.bfoot s), f c.f)
    [[[%8 bfoot cfoot] s=s r=r.cfoot] m]
  ::
      [%9 b=@ c=*]
    =^  cfoot  m  $(f c.f)
    =^  coot   m  (sockf r.cfoot (yarn r.cfoot b.f))
    [[[%9 b.f cfoot coot] s (cort coot)] m]
  ::
      [%10 [b=@ c=*] d=*]
    =^  cfoot  m  $(f c.f)
    =^  dfoot  m  $(f d.f)
    [[[%10 [b.f cfoot] dfoot] s (knit r.dfoot b.f r.cfoot)] m]
  ::
      [%11 b=@ c=*]
    =^  cfoot  m  $(f c.f)
    [[[%11 b.f cfoot] s r=r.cfoot] m]
  ::
      [%11 [b=@ c=*] d=*]
    =^  cfoot  m  $(f c.f)
    ::  implement the %data hint
    ::  delete the axes which are looked up in the hint from the subject
    ::  knowledge for the hinted computation
    ?:  =(b.f %data)
      =/  c  c.f
      |-
      ?:  ?=  [[%0 @] *]  c
        =.  s  (knit s ->.c [%gues ~])
        $(c +.c)
      =^  dfoot  m  ^$(f d.f)
      [[[%11 [b.f cfoot] dfoot] s r.dfoot] m]
    ?:  &(=(b.f %fast) ?=([%1 @ *] c.f))
      ~&  "%fast hint {<(,@tas +<.c.f)>}"
      ~|  "labl {<labl>} does not go to black hole"
      ?>  =((~(get by m) labl) [~ [~ ~]])
      =.  m  (~(put by m) labl [~ `+<.c.f])
      =^  dfoot  m  $(f d.f)
      [[[%11 [b.f cfoot] dfoot] s r.dfoot] m]
    =^  dfoot  m  $(f d.f)
    [[[%11 [b.f cfoot] dfoot] s r.dfoot] m]
  ::
      [%12 ref=* path=*]
    =^  reffoot   m  $(f ref.f)
    =^  pathfoot  m  $(f path.f)
    [[[%12 reffoot pathfoot] s [%gues ~]] m]
  ==
  ::
  ++  sockf
    |=  [s=sock f=sock]
    ^-  [coot memo]
    ?.  ?=  [%know *]  f
      ~&  "Dyn: {<s>}"
      [[%dyn s] m]
    =/  jet  (juke jute s k.f)
    ?.  ?=  ~  jet
      ::  found a jet
      ~&  "jet: {<q.u.jet>}"
      [[%jet q.u.jet] m]
    ?~  mem=(~(get by m) [s k.f])
      :: memo miss
      =.  m  (~(put by m) [s k.f] [~ ~]) :: blackhole for recursive eval
      =.  labl  [s k.f]
      =^  res  m  ^$(s s, f k.f)
      ~&  "Miss: sock {<s>} formula {<k.f>}"
      =.  m  (~(jab by m) [s k.f] |=([(unit sock) nam=(unit @tas)] [`r.res nam]))
      [[%mis res] m] :: fill in result
    ?~  p.u.mem
      :: memo blackhole
      ~&  "Recur: sock {<[s]>} formula {<k.f>}"
      [[%rec s k.f] m]
    :: memo hit
    ~&  "Hit: sock {<[s]>} formula {<k.f>} result {<u.p.u.mem>}"
    [[%hit u.p.u.mem] m]
  --
::  example nocks for testing
++  nocs
  |%
  ++  dec
    !=
    !.
    =>
    =>  %ed
    |%
    ++  dec
      |=  x=@
      ~/  %dec
      ~>  %data.[x ~]
      ^-  @
      =|  d=@
      |-
      ^-  d=@
      ?:  =(.+(d) x)
        d
      $(d .+(d))
    --
    (dec 8)
  ++  ad
    !=
    !.
    =>
    =>  %ed
    |%
    ++  dec
      |=  x=@
      ~/  %dec
      ~>  %data.[x ~]
      ^-  @
      =|  d=@
      |-
      ^-  d=@
      ?:  =(.+(d) x)
        d
      $(d .+(d))
    ++  add
      |=  [x=@ y=@]
      ~/  %add
      ~>  %data.[x y ~]
      ^-  @
      |-
      ^-  @
      ?:  =(x 0)
        y
      $(x (dec x), y .+(y))
    --
    (add 5 8)
  --
--
