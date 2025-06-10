#include "./headers.h" 

/*@
lemma push_induction (pointer front
        , pointer second_last
        , pointer last)
  requires
      ptr_eq(front, second_last) || !addr_eq(front, second_last);
      take Q = QueueAux(front, second_last);
      take Second_last = Owned<struct queue_cell>(second_last);
      ptr_eq(Second_last.next, last);
      take Last = Owned<struct queue_cell>(last);
  ensures
      ptr_eq(front, last) || !addr_eq(front, last);
      take Q_post = QueueAux(front, last);
      take Last2 = Owned<struct queue_cell>(last);
      Q_post == Snoc(Q, Second_last.first);
      Last == Last2;

@*/

