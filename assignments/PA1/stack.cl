(*
 *  CS164 Fall 94
 *
 *  Programming Assignment 1
 *    Implementation of a simple stack machine.
 *
 *  Skeleton file
 *)

class Main inherits IO {
    isX : Bool <- false;
    top : Node;

    main() : Object {
        (let inString : String in
            while not isX 
            loop {
                out_string(">");
                inString <- in_string();
                if inString = "x" then (new XCommand).excute(self, inString) else
                if inString = "d" then (new DCommand).excute(self, inString) else
                if inString = "e" then (new ECommand).excute(self, inString) else
                (new PushCommand).excute(self, inString)
                fi fi fi;
            }
            pool
        )
    };

    changeFlag() : Object {
        isX <- not isX
    };

    getTop() : Node {
        top
    };

    changeTop(n : Node) : Node {
        top <- n
    };
};

(*
    Node 定义了链表的节点
*)
class Node {
    value : String;
    next : Node;

    init(v : String, n : Node) : SELF_TYPE {{
        value <- v;
        next <- n;
        self;
    }};

    getValue() : String {
        value
    };

    changeValue(v : String) : SELF_TYPE {{
        value <- v;
        self;
    }};

    getNext() : Node {
        next
    };
};

class StackCommand inherits IO {
    excute(body : Main, command: String) : Object {
        out_string("Undefined StackCommand")
    };
};

class XCommand inherits StackCommand {
    excute(body : Main, command: String) : Object {
        body.changeFlag()
    };
};

class DCommand inherits StackCommand {
    excute(body : Main, command: String) : Object {
        (let n : Node <- body.getTop() 
        in 
            while not isvoid(n) loop {
                out_string(n.getValue());
                out_string("\n");
                n <- n.getNext();
            }
            pool
        )
    };
};

class PushCommand inherits StackCommand {
    excute(body : Main, command : String) : Object {
        (let n : Node <- (new Node).init(command, body.getTop()) 
        in 
            body.changeTop(n)  -- 入栈
        )
    };
};

class ECommand inherits StackCommand {
    excute(body : Main, command : String) : Object {
        (let top : Node <- body.getTop() 
        in 
            if not isvoid(top) then 
                if top.getValue() = "+" then
                    (let node1 : Node <- top.getNext(), 
                        node2 : Node <- node1.getNext() 
                    in
                        (let value1 : Int <- (new A2I).c2i(node1.getValue()), 
                            value2 : Int <- (new A2I).c2i(node2.getValue()) 
                        in
                            {
                                node2.changeValue((new A2I).i2c(value1 + value2));
                                body.changeTop(node2);
                            }
                        )
                    )
                else if top.getValue() = "s" then
                    (let node1 : Node <- top.getNext(), 
                        node2 : Node <- node1.getNext() 
                    in
                        (let value1 : String <- node1.getValue(), 
                            value2 : String <- node2.getValue() 
                        in
                            {
                                node2.changeValue(value1);
                                node1.changeValue(value2);
                                body.changeTop(node1);
                            }
                        )
                    )
                else true -- 头为数字
                fi fi
            else true -- 链表为空
            fi
        )
    };
};
