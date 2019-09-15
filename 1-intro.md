# Introduction: Computer Systems from a Verification Perspective
a more principled perspective 
...but you can call anything principled

specifically: specification + correctness + proofs
    Easy to tell if you have bugs; hard to tell you don't have bugs

what's a good specification, ...

## concrete motivation: BUGS!
why? they cause problems...

complexity -> bugs -> problems for end users

system has many requirements that cause complexity:
    performance
    security
    concurrency
    distributed systems
    fault tolerance
    evolution

bugs: might have seen memory errors, null pointers; we care more about subtle issues

problems:
    lose data
    corrupt data
    leak data

want to avoid bugs while still fulfilling requirements

## example: fault-tolerance in storage systems
power outage
defects (disk fails, bad blocks)

failure model: "fail-stop"
    e.g. power outage, disk failure
    nothing happens halfway
    but even with simple model, lots of systems have to worry about these faults
        one-node: FS, DBs, key-value stores
        distributed: key-value store, distributed database
        low-level: "flash translation layer" in SSD, handling complex requests, don't handle power outages all that well
    what do we want when this happens?
        system-level: should be able to restart
        user-level: ???
    challenge: crash-safety
    problems:
        1. inconsistent state
        2. concurrent writes
        3. optimizations
        4. partial failure (topic today)

[spooky filesystems chart]

filesystems: write-ahead logging
on disk: have a header "number of valid entries in log", and a log: list of blocks, and a data area: where data actually lives
log exists to help write data in a consistent way

to atomically write:
    figure out blocks you want to change:
    extend log: at address A, write b, at address c, write d
    *commit point*: say "we wrote these blocks"
    write blocks to disk
    truncate log

problem: disk can reorder writes!
-> need a SATA barrier between extend log and write data
...AND between write and truncate (otherwise, truncate can go through before write)

has to be okay to write blocks multiple times: idempotent

also has to be safe to crash during recovery!

(* this is a funny story, because the DB people figured this out 30 years ago, and the FS people didn't pay any attention. Moral: look around you!)

problem: this is slow!

## 2 logging optimizations
(could't be activated at the same time in Linux for 7 years!)

optimization 1: checksum logging
    can we skip barrier, extend log + update header at same time?
    yes: set header to be length + checksum of log blocks
        if checksum doesn't match log, throw out the log
    good optimization: halves forced disk writes
    * but what if header write is non-atomic??

optimization 2: log bypass writes
    - write data
    - log metadata
    - barrier
    - update header

there's a sneaky bug here! symptom: on crash writing large file, system booted up, blocks were wrong!
    because: combining both removes both barriers!

# so how do we avoid bugs?
testing -> incomplete
model checking -> large systems have too many states
verification -> *prove* no bugs (with some assumptions)

you should prolly use all of these

verification system: takes in spec, code, and (optionally) proof

can build different systems for different kinds of things

verification successes:
    CompCert c compiler
    amazon
    crypto in browsers:
        elliptic curve impl in google chrome has been formally verified in Coq.
    research prototypes: kernels, filesystems, distributed systems

verification is *hard*:
    hard to write a good spec.
        sufficient for callers: all the stuff your callers might care about
        precise
        succinct -> avoid unnecessary details
    code.
        often pretty short; difficult to verify large systems
        try to verify "core" even if you can't prove anything
    hard to write a good proof.
        the "grunge work"

# class structure



