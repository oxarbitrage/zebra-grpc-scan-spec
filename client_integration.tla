------------------------- MODULE client_integration -------------------------
(***************************************************************************)
(* External client support for Zebra specification                         *)
(*                                                                         *)
(* The specs simulates a call to the create_account grpc method as a       *)
(* starting point and then the grpc method calls the create_account        *)
(* procedure in the zcash_client_backend side. The grpc method then sends  *)
(* the key to the memory wallet and the memory wallet adds the key to the  *)
(* accounts set. The memory wallet then sends a block to the memory wallet *)
(* and the memory wallet adds the block to the blocks set.                 *)
(*                                                                         *)
(* The memory wallet is a simple algorithm that listens for requests and   *)
(* sends adding requests to the scan task. The scan task listens for       *)
(* requests from the services process and adds tasks to the scan task set. *)
(* The scan task also adds account to the memory wallet and either sends   *)
(* "scanned" blocks to the memory wallet or does nothing more.             *)
(*                                                                         *)
(* The main process is the entry point of the model and calls the          *)
(* create_account grpc method.                                             *)
(*                                                                         *)
(***************************************************************************)
EXTENDS TLC, Integers, Sequences, Json, FiniteSets

StatusWaiting == "waiting"
StatusAdding == "adding"
CreateAccountServiceRequest == "create_account"

(*--algorithm client_integration

variables
    \* A string that will be used as a response to any of the gRPC method calls, initially empty.
    response = "";
    \* The current service request flag, initially listening for requests.
    service_request = StatusWaiting;
    \* The current status of the scan task, initially listening for requests.
    scan_task_status = StatusWaiting;
    \* The set of scan tasks that are currently being processed, initially empty.
    scan_tasks = {};
    \* The key that will be served to the client after a create account request.
    key_to_be_served = "";
    \* The block that will be served to the client after a scan task finds a relevant block, initially empty.
    block_to_be_served = [height |-> 0, hash |-> "000000"];
    \* The set of accounts that in the memory wallet, initially empty.
    accounts = {};
    \* The set of blocks in the memory wallet, initially empty.
    blocks = {};
    \* Keep track of the last inserted accouint id.
    last_account_id = 0;

define
    \* Ensure that whenever a block is available, it eventually gets inserted into the memory wallet.
    LIVENESS_BLOCK_INSERTION ==
        /\ block_to_be_served.height > 0
        => <>(\A b \in blocks : b = block_to_be_served)
    \* Ensure that an account is not added twice.
    SAFETY_ACCOUNT_ADDITION ==
        /\ \A a \in accounts : 
                /\ a.account_id >= 0
                /\ \A b \in accounts : b.account_id # a.account_id
    \* Ensure that the account id is incremented properly.
    SAFETY_ACCOUNT_ID_INCREMENT ==
        /\ \A a, b \in accounts : a.account_id < b.account_id
    \* Ensure that a block is not inserted multiple times.
    SAFETY_BLOCK_INSERTION ==
        /\ \A b \in blocks : 
                /\ b.height > 0
                /\ \A c \in blocks : c.height # b.height
    \* Ensure that the service request always return to listening after adding.
    SERVICE_REQUEST_TRANSITION ==
        /\ service_request = StatusAdding 
            => <> (service_request = StatusWaiting)
    \* Ensure that all accounts have a non empty ufvk and that blocks have non zero hash.
    INDUCTIVE_INVARIANT ==
        /\ (\A acc \in accounts: acc.ufvk /= "")
        /\ (\A blk \in blocks: blk.hash /= "000000")
        /\ service_request \in {StatusWaiting, StatusAdding, CreateAccountServiceRequest}
end define;

\* UTILITY PROCEDURES:

(*-- Procedure to initiate the gRPC call for account creation.
    This sets the service_request flag to signal that an account creation request
    has been received and is being processed. *)
procedure create_account_grpc()
begin
    CreateAccountGrpc:
        service_request := CreateAccountServiceRequest;
end procedure;

\* The `create_account` in the zcash_client_backend side.
procedure create_account_zcash_client_backend()
begin
    CreateAccountZcashClientBackend:
        response := "zxviews...";
        return;
end procedure;

\* The `put_block` in the zcash_client_backend side.
procedure put_block_zcash_client_backend()
begin
    PutBlockZcashClientBackend:
        blocks := blocks \union {block_to_be_served};
end procedure;

\* SERVICES PROCESS:

\* Listen for requests and send adding requests to scan task.
process services = "SERVICES"
begin
    Services:
        \* We only have one service request in this algorithm.
        if service_request = CreateAccountServiceRequest then
            CallZcashClientBackend:
                call create_account_zcash_client_backend();
            SendKey:
                key_to_be_served := response;
            CreateAccount:
                scan_task_status := StatusAdding;
        end if;
    ServicesLoop:
        goto Services;
end process;


\* SCAN TASK PROCESS:

(* Listen for requests from the services process and:
- Add tasks to the scan task set.
- Add account to the memory wallet.
- Either send "scanned" blocks to the memory wallet or do nothing more.
*)
process scantask = "SCAN TASK"
variables inner_state = {}, inner_accounts = {}, inner_blocks = {}, inner_last_account_id = 0;
begin
    GetGlobals:
        inner_state := scan_tasks;
        inner_accounts := accounts;
        inner_last_account_id := last_account_id;
    ScanTask:
        if scan_task_status = StatusAdding then
            AddingAccount:
                accounts := inner_accounts \union {[account_id |-> last_account_id + 1, ufvk |-> key_to_be_served]};
                scan_tasks := inner_state \union {key_to_be_served};
                scan_task_status := StatusWaiting;
                last_account_id := inner_last_account_id + 1;
        end if;
    SendBlock:
        either
            block_to_be_served := [height |-> 1, hash |-> "111111"];
            call put_block_zcash_client_backend();
        or
            skip;
        end either;
    ScanTaskLoop:
        goto ScanTask;
end process;

\* MAIN PROCESS:

process Main = "MAIN"
begin
    CreteAccountCall:
        \* The grpc is the entry point of the model.
        call create_account_grpc();
    End:
        skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "83f024a5" /\ chksum(tla) = "971a54d7")
VARIABLES response, service_request, scan_task_status, scan_tasks, 
          key_to_be_served, block_to_be_served, accounts, blocks, 
          last_account_id, pc, stack

(* define statement *)
LIVENESS_BLOCK_INSERTION ==
    /\ block_to_be_served.height > 0
    => <>(\A b \in blocks : b = block_to_be_served)

SAFETY_ACCOUNT_ADDITION ==
    /\ \A a \in accounts :
            /\ a.account_id >= 0
            /\ \A b \in accounts : b.account_id # a.account_id

SAFETY_ACCOUNT_ID_INCREMENT ==
    /\ \A a, b \in accounts : a.account_id < b.account_id

SAFETY_BLOCK_INSERTION ==
    /\ \A b \in blocks :
            /\ b.height > 0
            /\ \A c \in blocks : c.height # b.height

SERVICE_REQUEST_TRANSITION ==
    /\ service_request = StatusAdding
        => <> (service_request = StatusWaiting)

INDUCTIVE_INVARIANT ==
    /\ (\A acc \in accounts: acc.ufvk /= "")
    /\ (\A blk \in blocks: blk.hash /= "000000")
    /\ service_request \in {StatusWaiting, StatusAdding, CreateAccountServiceRequest}

VARIABLES inner_state, inner_accounts, inner_blocks, inner_last_account_id

vars == << response, service_request, scan_task_status, scan_tasks, 
           key_to_be_served, block_to_be_served, accounts, blocks, 
           last_account_id, pc, stack, inner_state, inner_accounts, 
           inner_blocks, inner_last_account_id >>

ProcSet == {"SERVICES"} \cup {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ response = ""
        /\ service_request = StatusWaiting
        /\ scan_task_status = StatusWaiting
        /\ scan_tasks = {}
        /\ key_to_be_served = ""
        /\ block_to_be_served = [height |-> 0, hash |-> "000000"]
        /\ accounts = {}
        /\ blocks = {}
        /\ last_account_id = 0
        (* Process scantask *)
        /\ inner_state = {}
        /\ inner_accounts = {}
        /\ inner_blocks = {}
        /\ inner_last_account_id = 0
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "SERVICES" -> "Services"
                                        [] self = "SCAN TASK" -> "GetGlobals"
                                        [] self = "MAIN" -> "CreteAccountCall"]

CreateAccountGrpc(self) == /\ pc[self] = "CreateAccountGrpc"
                           /\ service_request' = CreateAccountServiceRequest
                           /\ pc' = [pc EXCEPT ![self] = "Error"]
                           /\ UNCHANGED << response, scan_task_status, 
                                           scan_tasks, key_to_be_served, 
                                           block_to_be_served, accounts, 
                                           blocks, last_account_id, stack, 
                                           inner_state, inner_accounts, 
                                           inner_blocks, inner_last_account_id >>

create_account_grpc(self) == CreateAccountGrpc(self)

CreateAccountZcashClientBackend(self) == /\ pc[self] = "CreateAccountZcashClientBackend"
                                         /\ response' = "zxviews..."
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED << service_request, 
                                                         scan_task_status, 
                                                         scan_tasks, 
                                                         key_to_be_served, 
                                                         block_to_be_served, 
                                                         accounts, blocks, 
                                                         last_account_id, 
                                                         inner_state, 
                                                         inner_accounts, 
                                                         inner_blocks, 
                                                         inner_last_account_id >>

create_account_zcash_client_backend(self) == CreateAccountZcashClientBackend(self)

PutBlockZcashClientBackend(self) == /\ pc[self] = "PutBlockZcashClientBackend"
                                    /\ blocks' = (blocks \union {block_to_be_served})
                                    /\ pc' = [pc EXCEPT ![self] = "Error"]
                                    /\ UNCHANGED << response, service_request, 
                                                    scan_task_status, 
                                                    scan_tasks, 
                                                    key_to_be_served, 
                                                    block_to_be_served, 
                                                    accounts, last_account_id, 
                                                    stack, inner_state, 
                                                    inner_accounts, 
                                                    inner_blocks, 
                                                    inner_last_account_id >>

put_block_zcash_client_backend(self) == PutBlockZcashClientBackend(self)

Services == /\ pc["SERVICES"] = "Services"
            /\ IF service_request = CreateAccountServiceRequest
                  THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "CallZcashClientBackend"]
                  ELSE /\ pc' = [pc EXCEPT !["SERVICES"] = "ServicesLoop"]
            /\ UNCHANGED << response, service_request, scan_task_status, 
                            scan_tasks, key_to_be_served, block_to_be_served, 
                            accounts, blocks, last_account_id, stack, 
                            inner_state, inner_accounts, inner_blocks, 
                            inner_last_account_id >>

CallZcashClientBackend == /\ pc["SERVICES"] = "CallZcashClientBackend"
                          /\ stack' = [stack EXCEPT !["SERVICES"] = << [ procedure |->  "create_account_zcash_client_backend",
                                                                         pc        |->  "SendKey" ] >>
                                                                     \o stack["SERVICES"]]
                          /\ pc' = [pc EXCEPT !["SERVICES"] = "CreateAccountZcashClientBackend"]
                          /\ UNCHANGED << response, service_request, 
                                          scan_task_status, scan_tasks, 
                                          key_to_be_served, block_to_be_served, 
                                          accounts, blocks, last_account_id, 
                                          inner_state, inner_accounts, 
                                          inner_blocks, inner_last_account_id >>

SendKey == /\ pc["SERVICES"] = "SendKey"
           /\ key_to_be_served' = response
           /\ pc' = [pc EXCEPT !["SERVICES"] = "CreateAccount"]
           /\ UNCHANGED << response, service_request, scan_task_status, 
                           scan_tasks, block_to_be_served, accounts, blocks, 
                           last_account_id, stack, inner_state, inner_accounts, 
                           inner_blocks, inner_last_account_id >>

CreateAccount == /\ pc["SERVICES"] = "CreateAccount"
                 /\ scan_task_status' = StatusAdding
                 /\ pc' = [pc EXCEPT !["SERVICES"] = "ServicesLoop"]
                 /\ UNCHANGED << response, service_request, scan_tasks, 
                                 key_to_be_served, block_to_be_served, 
                                 accounts, blocks, last_account_id, stack, 
                                 inner_state, inner_accounts, inner_blocks, 
                                 inner_last_account_id >>

ServicesLoop == /\ pc["SERVICES"] = "ServicesLoop"
                /\ pc' = [pc EXCEPT !["SERVICES"] = "Services"]
                /\ UNCHANGED << response, service_request, scan_task_status, 
                                scan_tasks, key_to_be_served, 
                                block_to_be_served, accounts, blocks, 
                                last_account_id, stack, inner_state, 
                                inner_accounts, inner_blocks, 
                                inner_last_account_id >>

services == Services \/ CallZcashClientBackend \/ SendKey \/ CreateAccount
               \/ ServicesLoop

GetGlobals == /\ pc["SCAN TASK"] = "GetGlobals"
              /\ inner_state' = scan_tasks
              /\ inner_accounts' = accounts
              /\ inner_last_account_id' = last_account_id
              /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTask"]
              /\ UNCHANGED << response, service_request, scan_task_status, 
                              scan_tasks, key_to_be_served, block_to_be_served, 
                              accounts, blocks, last_account_id, stack, 
                              inner_blocks >>

ScanTask == /\ pc["SCAN TASK"] = "ScanTask"
            /\ IF scan_task_status = StatusAdding
                  THEN /\ pc' = [pc EXCEPT !["SCAN TASK"] = "AddingAccount"]
                  ELSE /\ pc' = [pc EXCEPT !["SCAN TASK"] = "SendBlock"]
            /\ UNCHANGED << response, service_request, scan_task_status, 
                            scan_tasks, key_to_be_served, block_to_be_served, 
                            accounts, blocks, last_account_id, stack, 
                            inner_state, inner_accounts, inner_blocks, 
                            inner_last_account_id >>

AddingAccount == /\ pc["SCAN TASK"] = "AddingAccount"
                 /\ accounts' = (inner_accounts \union {[account_id |-> last_account_id + 1, ufvk |-> key_to_be_served]})
                 /\ scan_tasks' = (inner_state \union {key_to_be_served})
                 /\ scan_task_status' = StatusWaiting
                 /\ last_account_id' = inner_last_account_id + 1
                 /\ pc' = [pc EXCEPT !["SCAN TASK"] = "SendBlock"]
                 /\ UNCHANGED << response, service_request, key_to_be_served, 
                                 block_to_be_served, blocks, stack, 
                                 inner_state, inner_accounts, inner_blocks, 
                                 inner_last_account_id >>

SendBlock == /\ pc["SCAN TASK"] = "SendBlock"
             /\ \/ /\ block_to_be_served' = [height |-> 1, hash |-> "111111"]
                   /\ stack' = [stack EXCEPT !["SCAN TASK"] = << [ procedure |->  "put_block_zcash_client_backend",
                                                                   pc        |->  "ScanTaskLoop" ] >>
                                                               \o stack["SCAN TASK"]]
                   /\ pc' = [pc EXCEPT !["SCAN TASK"] = "PutBlockZcashClientBackend"]
                \/ /\ TRUE
                   /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTaskLoop"]
                   /\ UNCHANGED <<block_to_be_served, stack>>
             /\ UNCHANGED << response, service_request, scan_task_status, 
                             scan_tasks, key_to_be_served, accounts, blocks, 
                             last_account_id, inner_state, inner_accounts, 
                             inner_blocks, inner_last_account_id >>

ScanTaskLoop == /\ pc["SCAN TASK"] = "ScanTaskLoop"
                /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTask"]
                /\ UNCHANGED << response, service_request, scan_task_status, 
                                scan_tasks, key_to_be_served, 
                                block_to_be_served, accounts, blocks, 
                                last_account_id, stack, inner_state, 
                                inner_accounts, inner_blocks, 
                                inner_last_account_id >>

scantask == GetGlobals \/ ScanTask \/ AddingAccount \/ SendBlock
               \/ ScanTaskLoop

CreteAccountCall == /\ pc["MAIN"] = "CreteAccountCall"
                    /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "create_account_grpc",
                                                               pc        |->  "End" ] >>
                                                           \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "CreateAccountGrpc"]
                    /\ UNCHANGED << response, service_request, 
                                    scan_task_status, scan_tasks, 
                                    key_to_be_served, block_to_be_served, 
                                    accounts, blocks, last_account_id, 
                                    inner_state, inner_accounts, inner_blocks, 
                                    inner_last_account_id >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << response, service_request, scan_task_status, scan_tasks, 
                       key_to_be_served, block_to_be_served, accounts, blocks, 
                       last_account_id, stack, inner_state, inner_accounts, 
                       inner_blocks, inner_last_account_id >>

Main == CreteAccountCall \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == services \/ scantask \/ Main
           \/ (\E self \in ProcSet:  \/ create_account_grpc(self)
                                     \/ create_account_zcash_client_backend(self)
                                     \/ put_block_zcash_client_backend(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
