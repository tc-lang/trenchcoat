# Concurrency in TrenchCoat

Concurrency is a requirement for modern, large scale projects. Whether it be a server handling thousonds od requests, or a user application performing some heavy CPU work utilizing the many cores that most consumer compuers now have.

TrenchCoat aims to highly abstract concurrency, making it simple, easy, and safe - but with little to no cost, perhaps even a negative cost compared to using a traditional threaded approach.

TrenchCoat has 4 concurrency modes, each with different purposes. For most projects, you don't need to understand or even be aware of these; the compiler will choose for you, and in 99% of cases it will choose right.
The aim of this document is to give a brief explanation of what the modes are to give to an appreciation of what's going on under the hood and to make you aware of when switching from the default could benifit your project.

## A brief overview

### No runtime modes

#### (disabled) No concurrency mode
In no concurrency mode, the compiler does not allow concurrency through the language. You may still use libraries to spawn OS threads, however the compiler will not be aware of these. It will not make specific optimisations for it or enforce any safety rules around concurrent access. If you choose to spawn threads manually, then the responsibility is yours.

Concurrency related language features are disabled when in this mode, resulting in a compile time error if they are used.

#### (os) OS thread mode
In OS thread mode, the compiler enables concurrency features, but every time a new goroutine (or shall we call them coats?) is started, a new operating system thread is started. This comes with quite a bit of overhead and resitrictions on thread numbers etc by the OS. This is however fine for programs which only use a small number of long running goroutines - minimising the start/stop overhead from the OS and not encountering any overhead from the runtime - including a reduction in binary size due to the runtime not being included.

### Runtime modes
Each runtime mode has 2 sub-modes: threaded and non-threaded. In non-threaded mode, the program is run in a single thread, whereas in threaded mode, the runtime may spawn multiple operating system threads and distribute the work among them. The number of threads spawned can be user defined or, by default, decided at runtime based on the number of CPU cores available.

The first main advantage of a runtime scheduling, is that the language runtime is more aware than the OS of what the program is doing; the runtime is aware of which locks are locked, and which goroutines are waiting on which channels, and can schedule accordingly. The second is the heavily reduced overhead. Spawning a goroutine has almost no overhead, especially when compared to creating a thread, and the program can be optimised by the compiler to reduce overhead when swtiching between them.

#### (queue) Queue Mode
In queue mode, when a new goroutine is spawned, it is added to the back of the queue. The runtime then executes goroutines from the front of the queue. It will then wait until either the goroutine terminates, or the goroutine makes a call to the scheduler, indicating that it would like to be moved to the back of the queue.
Queue mode may also alter the order of the queue based on facts it knows about what a goroutine is waiting for and if it is ready or not. The exact behaviour of the queue is not defined.

This method has very little overhead, however - when used on a server especially - can be problematic since a goroutine may get in to an infinite loop and never terminate or call the scheduler. In this case, the thread it is executing on will not move on to another goroutine. This can cause threads to lock up. In the case of a server, this would cause it to become unresponsive since no other code would get a chance to service another request. This also could lead to a DOS attack, where an attacker causes a goroutine to run for a long time (for example by exploiting a badly written, or just complex, regexp, or exploiting a bug found in the code which causes a long running loop, or even worse, a non-terminating one), and flooding the server with such requests, causing big delays in the servicing of requests.

TODO: Maybe we should give this mode a better name?

#### (full) Full mode
In full mode, the schedular operates as queue mode did, but with the added addition of a timer to prevent goroutines from executing excesive periods of time before yielding. This means that even if a goroutine takes a long time to execute on a server, other requests will still be serviced. This has the same effect of spawning a thread for every goroutine, however with segnificantly lower overhead, and the advantage of the schedular being more aware of what the program is doing.

One downside to full mode, is that is relies upon alarm signals from the operating system. This means that you cannot handle these signals yourself.

## How the compiler chooses a mode
To start with, if your code never uses goroutines, then there's no need for any of this, so no concurrency mode is used!

If your program does use goroutines, then full mode is selected by default. Full mode has very little overhead and is the best concurrency method for on average and the best, flat out, in a lot of cases.

If though, you know that your program would benifit from having an OS thread per goroutine, then you may want to choose OS thread mode. If you know that your program will be okay with threads locking up, since you just need the computation doing, then you may want to choose queue mode, to remove the overhead of timeouts. Or, if you need to be able to handle signals directly, then you may wish to choose a mode other than full mode which is the most suited to your program - note that if you are heavily spawning goroutines, then OS thread mode will carry a lot of overhead. However if possible, needing the handle alarm signals should be avoided.

If you want to manually select a mode, then you can pass the --concurreny-mode flag to the compiler, with one of the following values:
- disabled
- os
- queue
- full

Note that if concurrency-mode is set to disable, and the targetted code using a concurrency feature, then an error will be triggered.

## Changing the behaviour of your code to suit the concurrency mode.

When writing a library, you may wish to behave differently depending on the concurrency mode the user has opted for.
For example, you may wish to distribute an algorithm accross multiple goroutines, but yet, if that will carry heavy overhead, for example is OS thread mode, you might not want to - or you may only want to at a much higher threshold. You might also wish for your library to only use a concurrency feature if the compiler is compiling with it enabled; allowing your library to be used with concurrency disabled, but also take advantage of concurrency when it exists.

TODO: Decide how to do this - it should be with the rest of the conditional compilation stuff.

