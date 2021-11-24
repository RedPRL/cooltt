(** Thread-Safe Job Queues, with blocking reads.

    The model here is that we have a single "read" queue,
    which may spawn off many workers that can write messages. *)

type read
type write

(** A simple, thread-safe queue. *)
type ('mode, 'a) t

type 'a read_t = (read, 'a) t
type 'a write_t = (write, 'a) t

(** Create a new job queue. *)
val create : unit -> (read, 'a) t

(** Create a worker queue that may write to the original queue. *)
val worker : (read, 'a) t -> (write, 'a) t

(** Create a queue that discards any messages placed on it. *)
val null : (write, 'a) t

(** Place a message onto the job queue. *)
val enqueue : 'a -> (write, 'a) t -> unit

(** Grab a message off the job queue, blocking if the queue is empty. *)
val dequeue : (read, 'a) t -> 'a

(** Dequeue all messages off the queue. This will not block if the queue is empty. *)
val drain : (read, 'a) t -> 'a Seq.t
