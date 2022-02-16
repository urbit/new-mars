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
+$  memo  (map [sock *] [(unit sock) (unit @tas)])
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
  =|  memo=memo
  |=  [s=sock f=*]
  ^-  [sock _memo]
  |-
  ^-  [sock _memo]
  =/  sockf
    |=  [s=sock f=sock] 
    ^-  [sock _memo]
    ?.  ?=  [%know *]  f
      [[%gues ~] memo]
    =/  m  (~(get by memo) s k.f)
    ?~  m
      :: memo miss
      =.  memo  (~(put by memo) [s k.f] [~ ~])
      =^  r  memo  ^$(s s, f +.f)
      [r (~(put by memo) [s k.f] [`r ~])] 
    ?~  -.u.m
      ::  memo blackhole
      [[%gues ~] memo]
    ::  memo hit]
    [u.-.u.m memo]
  ?+  f  ~|(%wash-bonk !!)
      [[* *] *]
    =^  pres  memo  $(f -.f)
    =^  qres  memo  $(f +.f)
    [(both pres qres) memo]
  ::
      [%0 b=@]
    [(yarn s b.f) memo]
  ::
      [%1 b=*]
    [[%know b.f] memo]
  ::
      [%2 b=* c=*]
    =^  bres  memo  $(f b.f)
    =^  cres  memo  $(f c.f)
    (sockf s=bres f=cres)
  ::
      [%3 b=*]
    =^  bres  memo  $(f b.f)
    [(deep bres) memo]
  ::
      [%4 b=*]
    =^  bres  memo  $(f b.f)
    [[%gues ~] memo]
  ::
      [%5 b=* c=*]
    =^  bres  memo  $(f b.f)
    =^  cres  memo  $(f c.f)
    [(pear bres cres) memo]
  ::
      [%6 b=* c=* d=*]
    =^  bres  memo  $(f b.f)
    ?+  bres  ~|(%wash-nest !!)
        [%know %0]
      $(f c.f)
    ::
        [%know %1]
      $(f d.f)
    ::  can we merge them somehow in this case? things the branches
    ::  agree on?
        [%gues ~]
      [[%gues ~] memo]
    ==
  ::
      [%7 b=* c=*]
    =^  bres  memo  $(f b.f)
    $(s bres, f c.f)
  ::
      [%8 b=* c=*]
    =^  bres  memo  $(f b.f)
    $(s (both bres s), f c.f)
  ::
      [%9 b=@ c=*]
    =^  cres  memo  $(f c.f)
    (sockf cres (yarn cres b.f))
  ::
      [%10 [b=@ c=*] d=*]
    =^  cres  memo  $(f c.f)
    =^  dres  memo  $(f d.f)
    [(knit dres b.f cres) memo]
  ::
      [%11 b=@ c=*]
    $(f c.f)
  ::
      [%11 [b=@ c=*] d=*]
    =^  cres  memo  $(f c.f)
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
    =^  rres  memo  $(f ref.f)
    =^  pres  memo  $(f path.f)
    [[%gues ~] memo]
  ==
::
++  pull
  =|  memo=memo
  |=  [=jute s=sock f=*]
  ^-  [foot _memo]
  =/  labl  [s f]
  |^
  ^-  [foot _memo]
  ?+  f  ~|("unrecognized nock {<f>}" ~|(%pull-bonk !!))
      [[* *] *]
    =^  pfoot  memo  $(f -.f)
    =^  qfoot  memo  $(f +.f)
    [[[%cell pfoot qfoot] s (both r.pfoot r.qfoot)] memo]
  ::
      [%0 b=@]
    [[[%0 b.f] s=s r=(yarn s b.f)] memo]
  ::
      [%1 b=*]
    [[[%1 b.f] s=s r=[%know b.f]] memo]
  ::
      [%2 b=* c=*]
    =^  bfoot  memo  $(f b.f)
    =^  cfoot  memo  $(f c.f)
    =^  coot  memo  (sockf r.bfoot r.cfoot)
    [[[%2 bfoot cfoot coot] s (cort coot)] memo]
  ::
      [%3 b=*]
    =^  bfoot  memo  $(f b.f)
    [[[%3 bfoot] s (deep r.bfoot)] memo]
  ::
      [%4 b=*]
    =^  bfoot  memo  $(f b.f)
    [[[%4 bfoot] s [%gues ~]] memo]
  ::
      [%5 b=* c=*]
    =^  bfoot  memo  $(f b.f)
    =^  cfoot  memo  $(f c.f)
    [[[%5 bfoot cfoot] s (pear r.bfoot r.cfoot)] memo]
  ::
      [%6 b=* c=* d=*]
    =^  bfoot  memo  $(f b.f)
    ?+  r.bfoot  ~|(%pull-nest !!)
        [%know %0]
      =^  cfoot  memo  $(f c.f)
      [[[%6 bfoot `cfoot ~] s r.cfoot] memo]
    ::
        [%know %1]
      =^  dfoot  memo  $(f d/f)
      [[[%6 bfoot ~ `dfoot] s r.dfoot] memo]
    ::
        [%gues ~]
      =^  cfoot  memo  $(f c.f)
      =^  dfoot  memo  $(f d.f)
      [[[%6 bfoot `cfoot `dfoot] s [%gues ~]] memo]
    ==
  ::
      [%7 b=* c=*]
    =^  bfoot  memo  $(f b.f)
    =^  cfoot  memo  $(s r.bfoot, f c.f)
    [[[%7 bfoot cfoot] s r.cfoot] memo]
  ::
      [%8 b=* c=*]
    =^  bfoot  memo  $(f b.f)
    =^  cfoot  memo  $(s (both r.bfoot s), f c.f)
    [[[%8 bfoot cfoot] s=s r=r.cfoot] memo]
  ::
      [%9 b=@ c=*]
    =^  cfoot  memo  $(f c.f)
    =^  coot  memo  (sockf r.cfoot (yarn r.cfoot b.f))
    [[[%9 b.f cfoot coot] s (cort coot)] memo]
  ::
      [%10 [b=@ c=*] d=*]
    =^  cfoot  memo  $(f c.f)
    =^  dfoot  memo  $(f d.f)
    [[[%10 [b.f cfoot] dfoot] s (knit r.dfoot b.f r.cfoot)] memo]
  ::
      [%11 b=@ c=*]
    =^  cfoot  memo  $(f c.f)
    [[[%11 b.f cfoot] s r=r.cfoot] memo]
  ::
      [%11 [b=@ c=*] d=*]
    =^  cfoot  memo  $(f c.f)
    ::  implement the %data hint
    ::  delete the axes which are looked up in the hint from the subject
    ::  knowledge for the hinted computation
    ?:  =(b.f %data)
      =/  c  c.f
      |-
      ?:  ?=  [[%0 @] *]  c
        =.  s  (knit s ->.c [%gues ~])
        $(c +.c)
      =^  dfoot  memo  ^$(f d.f)
      [[[%11 [b.f cfoot] dfoot] s r.dfoot] memo]
    ?:  &(=(b.f %fast) ?=([%1 @ *] c.f))
      ~&  "%fast hint {<(,@tas +<.c.f)>}"
      ~|  "labl {<labl>} does not go to black hole"
      ?>  =((~(get by memo) labl) [~ [~ ~]])
      =.  memo  (~(put by memo) labl [~ `+<.c.f])
      =^  dfoot  memo  $(f d.f)
      [[[%11 [b.f cfoot] dfoot] s r.dfoot] memo]
    =^  dfoot  memo  $(f d.f)
    [[[%11 [b.f cfoot] dfoot] s r.dfoot] memo]
  ::
      [%12 ref=* path=*]
    =^  reffoot  memo  $(f ref.f)
    =^  pathfoot  memo  $(f path.f)
    [[[%12 reffoot pathfoot] s [%gues ~]] memo]
  ==
  ::
  ++  sockf
    |=  [s=sock f=sock]
    ^-  [coot _memo]
    ?.  ?=  [%know *]  f
      ~&  "Dyn: {<s>}"
      [[%dyn s] memo]
    =/  jet  (juke jute s k.f)
    ?.  ?=  ~  jet
      ::  found a jet
      ~&  "jet: {<q.u.jet>}"
      [[%jet q.u.jet] memo]
    =/  mem  (~(get by memo) [s k.f])
    ?~  mem
      :: memo miss
      =.  memo  (~(put by memo) [s k.f] [~ ~]) :: blackhole for recursive eval
      =.  labl  [s k.f]
      =^  res  memo  ^$(s s, f k.f)
      ~&  "Miss: sock {<s>} formula {<k.f>}"
      =.  memo  (~(jab by memo) [s k.f] |=([(unit sock) nam=(unit @tas)] [`r.res nam]))
      [[%mis res] memo] :: fill in result
    ?~  -.u.mem
      :: memo blackhole
      ~&  "Recur: sock {<[s]>} formula {<k.f>}"
      [[%rec s k.f] memo]
    :: memo hit
    ~&  "Hit: sock {<[s]>} formula {<k.f>} result {<u.u.mem>}"
    [[%hit u.-.u.mem] memo]
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
