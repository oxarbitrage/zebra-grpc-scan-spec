# zebra-grpc-scan-spec
Spec and design of the zebra-grpc scanner functionality


## Design diagram (v0.6):

```mermaid
flowchart TD
    zebra-scan([zebra-scan]) --> |Service|requests/responses(Requests / Responses\n#8182)
    zebra-node-services([zebra-node-services]) ---> |Request and response type signatures|requests/responses(Requests / Responses\n#8182)
    requests/responses ---> |Service call|info[(Info\n#8162)]
    requests/responses ---> |Service call|results[(Results\n#8205)]
    requests/responses ---> |Service call|register[(Register\n#8203)]
    requests/responses ---> |Service call|delete[(Delete\n#8204)]
    requests/responses ---> |Service call|clear[(Clear\n#8207)]
    requests/responses ---> |Service call|subscribe[(Subscribe\n#8206)]
    requests/responses ---> |Service call|status[(Status\n#8257)]
    
    getinfo(getinfo) ----> |gRPC method|zebra-grpc
    info ----> getinfo(getinfo\n#8162)
    getresults(getresults) ----> |gRPC method|zebra-grpc
    results ----> getresults(getresults\n#8163)
    registerkeys(registerkeys) ----> |gRPC method|zebra-grpc
    register ----> registerkeys(registerkeys\n#8176)
    deletekeys(deletekeys) ----> |gRPC method|zebra-grpc
    delete ----> deletekeys(deletekeys\n#8235)
    clear ----> clearresults(clearresults\n#8235)
    clearresults ----> |gRPC method|zebra-grpc
    register ----> scan
    results ----> scan
    subscribe ----> scan
    clear ----> |Not yet implemented|scan
    scan(scan\n#8256) ---> |gRPC push interface|zebra-grpc
    status ----> getstatus
    getstatus(getstatus\n#8258) ----> |gRPC method|zebra-grpc
    
    zebra-grpc([zebra-grpc]) ----> |username/password|client-auth(Client Auth\n#8164)
    zebra-grpc ----> |Address, port, etc|config(Configuration)
    zebra-grpc ----> |Encryption, TLS|server-auth(Server Auth)
    zebra-grpc ----> |All tests for the system|testing(Testing)
    
    zebrad([zebrad]) ----> |Zebrad starts the \nblockchain scanner task|zebra-scan
    zebrad ----> |Zebrad starts the grpc server\n#8241|zebra-grpc

    testing ---> |grpc responses|snapshots(gRPC Snapshots\n#8244)
    testing ---> |grpc requests & responses|grpc-unit(gRPC Unit tests\n#8244)
    testing ---> |service requests & responses|service-unit(Service Unit tests\nDone with each service impl)
    testing ---> |client|acceptance(Acceptance with state tests\n#8274 + #8259)
    testing ---> |grpcurl|manual(Manual testing\nDone with each grpc method impl)

    subgraph commands [Interaction between the services and the Scan Task]
        zebrad -..-> |Scan keys in the config|start-scan-task{{Start scan Task}}
        register -.-> start-scan-task
        delete -..-> stop-scan-task{{Stop scan task}}
        subscribe -..-> subscribe-scan-task{{Subscribe scan task}}
        zebra-scan --> scan-task{{Scan Task}}
        scan-task --> subscribe-scan-task
        scan-task --> start-scan-task
        scan-task --> stop-scan-task
        scan-task-refactor(Scan task refactor \n#8250) ----> scan-task
    end

    %% color of the nodes
    style zebra-scan fill:#8856eb
    style zebra-node-services fill:#8856eb
    style requests/responses fill:#8856eb
    style info fill:#8856eb
    style getinfo fill:#8856eb
    style results fill: #8856eb
    style getresults fill: #8856eb
    style register fill: #8856eb
    style registerkeys fill: #8856eb
    style zebra-grpc fill:#8856eb
    style delete fill:#8856eb
    style clear fill:#8856eb
    style deletekeys fill:#8856eb
    style clearresults fill:#8856eb
    style subscribe fill: #8856eb
    style zebrad fill: #8856eb
    style scan fill:#8856eb
    
    style config fill:#8856eb
    style testing fill:#8856eb

    style scan-task fill:#8856eb
    style start-scan-task fill:#8856eb
    style stop-scan-task fill:#8856eb
    style subscribe-scan-task fill:#8856eb

    style manual fill:#8856eb
    style acceptance fill:#238636
    style snapshots fill:#8856eb
    style grpc-unit fill:#8856eb
    style service-unit fill:#8856eb
```
