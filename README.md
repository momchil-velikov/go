## Loop Inversion

Loop Inversion enables Loop Invariant Code Motion to hoist more
invariants outside loops.

For a for loop
    
      for init; cond; inc {
          body
      }
    
the Go compiler generates
    
      <init>
      goto C
    B:
      <body>
      <inc>
    C:
      if <cond> goto B
    
In this form of loop translation, however, moving invariant expressions
outside of the loop is problematic as there isn't really a point, where
to place them, while making sure they aren't executed if the loop body
is never entered. Only invariants, which can be speculatively executed,
or invariants occuring in `<cond>`, can be placed right in front of the
initial jump to the loop condition.
    
If, instead, the loop is translated like
    
      <init>
      if !<cond> goto E
    B:
      <body>
      <inc>
     if <cond> goto B
    E:
    
loop invariants can be safely moved before the label `B`. The drawback
is that the code for evaluatung the condition is emitted twice.
