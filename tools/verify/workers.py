"""Runs a function on each item, each in a fresh process, a few at once.

A fresh process per item keeps the provers' memory flat (the normal forms'
caches in canon.py keep their terms alive). A worker that ends without a
result (the kernel's out-of-memory killer, a crash, an exception, whose
traceback it prints) stops the whole run with its item named:
multiprocessing.Pool would wait forever for the result it never sends.
The run's other workers are killed as it stops, so the stop is prompt:
the interpreter would otherwise wait at exit for each of them to finish
its item (a 60 s sibling held a stop for 60 s: BLAKE3 #131). The same
holds when the caller stops taking results early.
"""
import multiprocessing
from multiprocessing.connection import wait


def _run(fn, item, conn):
    conn.send(fn(item))


def each(fn, items, workers, context=multiprocessing):
    """Yields fn(item) for every item, in the order they finish, with at
    most `workers` (and at most one per CPU) running at once. fn and its
    items are picklable when `context` spawns."""
    todo, running = list(items), {}
    workers = min(workers, multiprocessing.cpu_count())
    try:
        while todo or running:
            while todo and len(running) < workers:
                item = todo.pop(0)
                here, there = context.Pipe(duplex=False)
                p = context.Process(target=_run, args=(fn, item, there))
                p.start()
                there.close()
                running[here] = (p, item)
            for conn in wait(list(running)):
                p, item = running.pop(conn)
                try:
                    result = conn.recv()
                except EOFError:
                    p.join()
                    raise SystemExit(f"the worker for {item!r} ended without a result, exit status {p.exitcode} "
                                     "(-9 is a kill, most often the kernel's out-of-memory killer: run fewer at once)")
                p.join()
                yield result
    finally:
        # Whatever stops the run (a worker's death, the caller's early
        # stop), the workers still running go with it.
        for p, _ in running.values():
            p.kill()
            p.join()
