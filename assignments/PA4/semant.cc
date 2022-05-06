

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <vector>
#include <algorithm>
#include <set>

extern int semant_debug;
extern char *curr_filename;


static int semant_errors = 0;
static ostream& error_stream = cerr;

std::map<Symbol, Class_> name_class_map;
std::map<Symbol, Symbol> parent_map;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name to type
ObjectEnvironment object_env;

typedef std::vector<method_class*> Methods;
typedef std::map<Class_, Methods> MethodTable;
MethodTable method_table;

static Class_ curr_class;

static ostream& semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

static ostream& semant_error(tree_node *t)
{
    error_stream << curr_class->get_filename() << ":" << t->get_line_number() << ": ";
    return semant_error();
}

static void exit_with_error() {
    if (semant_errors) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}


//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

static void add_class(Class_ c) {
    Symbol name = c->get_name();
    Symbol parent = c->get_parent();

    if(name == SELF_TYPE) {
        semant_error(c) << "Redefinition of basic class SELF_TYPE." << endl;
    }
    else if(name_class_map.count(name)) {
        semant_error(c) << "Class " << name << " was previously defined." << endl;
    }
    else if (parent == Int || parent == Str || parent == Bool || parent == SELF_TYPE) {
        semant_error(c) << "Class " << name << " cannot inherit class " << parent << "." << endl;
    }
    else {
        name_class_map[name] = c;
        parent_map[name] = parent;         
    }
}

static void install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    add_class(Object_class);
    add_class(IO_class);
    add_class(Int_class);
    add_class(Bool_class);
    add_class(Str_class);
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

// 检查环和父类存在
static void check_inheritance() {
    for (auto it = parent_map.begin(); it != parent_map.end(); it++){
        Symbol child = it->first;
        Symbol parent = it->second;

        // 根为No_class
        while (parent != No_class){
            // 存在环
            if (parent == child){
                semant_error(name_class_map[child]) << "Has cycle!" << endl;
                return;
            }
            // 不存在父节点
            if (!parent_map.count(parent)){
                semant_error(name_class_map[child]) << "Doesn't contain parent!" << endl;
                return;
            }
            parent = parent_map[parent];
        }
    }
}

static void check_main() {
    bool main_class_flag = false;
    bool main_method_flag = false;

    for (auto it = name_class_map.begin(); it != name_class_map.end(); it++){
        Symbol name = it->first;
        Class_ c = it->second;
        if (name == Main){
            main_class_flag = true;
            Features features = c->get_features();
            for (auto i = features->first(); features->more(i); i = features->next(i)){
                Feature feature = features->nth(i);
                if (feature->is_method() && feature->get_name() == main_meth){
                    main_method_flag = true;
                    break;
                }
            }
            break;
        }
    }

    if (!main_class_flag){
        semant_error() << "No main class!" << endl;
    }
    else if(!main_method_flag){
        semant_error() << "No 'main' method in class Main." << endl;
    }
}

// 初始化 methodTable
static void install_methods() {
    for(auto & it : name_class_map) {
        Features features = it.second->get_features();
        Methods methods;
        for (auto i = features->first(); features->more(i); i = features->next(i)){
            Feature feature = features->nth(i);
            if (feature->is_method()){
                method_class* method = static_cast<method_class*>(feature);

                bool existed = false;
                for (auto j = methods.begin(); j != methods.end(); j++){
                    if (method->get_name() == (*j)->get_name()){
                        existed = true;
                        break;
                    }
                }
                if (!existed){
                    methods.push_back(method);
                }
                else {
                    semant_error(method) << "Method " << method->get_name() << " is multiply defined." << endl;
                }
            }
        }
        method_table[it.second] = methods;
    }
}

// 调用此函数时，之前已经检查过继承关系了
static void get_inheritance_list(Class_ c, std::vector<Class_>& inheritance_list) {
    while (c->get_name() != Object){
        inheritance_list.push_back(c);
        if (name_class_map.count(c->get_parent()) == 0) {
            semant_error() << "Invalid inheritance!" << endl;
            break;
        }
        else
            c = name_class_map[c->get_parent()];
    }
    inheritance_list.push_back(name_class_map[Object]);
}

static void get_inheritance_list(Symbol name, std::vector<Class_>& inheritance_list) {
    if (name == SELF_TYPE)
        name = curr_class->get_name();
    if (name_class_map.count(name) == 0) 
        semant_error() << "Class " << name << " doesn't exist!" << endl;
    get_inheritance_list(name_class_map[name], inheritance_list);
}

static method_class* get_method(Class_ c, Symbol method_name) {
    Methods methods = method_table[c];
    for (size_t i = 0; i < methods.size(); i++)
        if (methods[i]->get_name() == method_name)
            return methods[i];
    return 0;
}


// 检查type1是type2的子类
static bool conform(Symbol type1, Symbol type2) {
    if (type1 == SELF_TYPE && type2 == SELF_TYPE)
        return true;
    if (type1 != SELF_TYPE && type2 == SELF_TYPE)
        return false;

    if (type1 == SELF_TYPE)
        type1 = curr_class->get_name();

    if (!name_class_map.count(type1))
        semant_error() << "Class " << type1 << " doesn't exist." << endl;
    if (!name_class_map.count(type2))
        semant_error() << "Class " << type2 << " doesn't exist." << endl;

    std::vector<Class_> inheritance_list1;

    get_inheritance_list(type1, inheritance_list1);
    for (auto & it : inheritance_list1) {
        if (it->get_name() == type2)
            return true;
    }
    return false;
}
    

static void check_methods() {
    for (auto & it : name_class_map) {
        Symbol class_name = it.first;
        curr_class = it.second;

        if (class_name == Object || class_name == IO || class_name == Int || class_name == Bool || class_name == Str){
            continue;
        }

        // 检查准备
        std::vector<Class_> inheritance_list;
        get_inheritance_list(curr_class, inheritance_list);
        for (auto & ancestor : inheritance_list) { // 对继承关系添加 attr
            Features features = ancestor->get_features();
            object_env.enterscope();
            for (auto i = features->first(); features->more(i); i = features->next(i)) {
                if (features->nth(i)->is_method()) continue;
                attr_class* attr = static_cast<attr_class*>(features->nth(i));
                object_env.addid(attr->get_name(), new Symbol(attr->get_type_decl()));
            }
        }

        // 检查开始
        Features features = curr_class->get_features();
        for (auto i = features->first(); features->more(i); i = features->next(i)) {
            Feature curr_feature = features->nth(i);
            if (curr_feature->is_method()) { // 检查方法
                method_class* curr_method = static_cast<method_class*>(curr_feature);
                curr_method->check_type();

                 // 查看继承关系
                for (auto & ancestor : inheritance_list) {
                    method_class* ancestor_method = get_method(ancestor, curr_method->get_name());
                    if (!ancestor_method) continue; // 没有

                    // 检查返回值
                    if (curr_method->get_return_type() != ancestor_method->get_return_type())
                        semant_error(curr_method) 
                            << "In redefined method " << curr_method->get_name() 
                            << ", return type " << curr_method->get_return_type() 
                            << " is different from original return type " << ancestor_method->get_return_type() << endl;

                    // 检查参数
                    Formals curr_formals = curr_method->get_formals();
                    Formals ancestor_formals = ancestor_method->get_formals();
                    int k1 = curr_formals->first();
                    int k2 = ancestor_formals->first();
                    
                    while (curr_formals->more(k1) && ancestor_formals->more(k2)) {
                        if (curr_formals->nth(k1)->get_type_decl() != ancestor_formals->nth(k2)->get_type_decl())
                            semant_error(curr_formals->nth(k1)) 
                                << "In redefined method " << curr_method->get_name() 
                                << ", parameter type " << curr_formals->nth(k1)->get_type_decl() 
                                << " is different from original type " << ancestor_formals->nth(k2)->get_type_decl() << endl;
                        k1 = curr_formals->next(k1);
                        k2 = ancestor_formals->next(k2);
                        if (curr_formals->more(k1) xor ancestor_formals->more(k2))
                            semant_error(curr_method) 
                                << "Incompatible number of formal parameters in redefined method " << curr_method->get_name() << endl;
                    }
                }
            }
            else { // 检查属性
                attr_class* curr_attr = static_cast<attr_class*>(curr_feature);
                curr_attr->check_type();
            }
        }

        for (auto & ancestor : inheritance_list) {
            object_env.exitscope();
        }
    }
}

// 方法的typecheck
void method_class::check_type() {
    object_env.enterscope();
    // 检查参数
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        Formal formal = formals->nth(i);
        if (formal->get_name() == self) {
            semant_error(formal) << "self cannot be used as formal parameter" << endl;
        }
        else if (object_env.lookup(formal->get_name()) != NULL)
            semant_error(formal) << "duplicate formal parameter " << formal->get_name() << endl;
        else if (name_class_map.count(formal->get_type_decl()) == 0)
            semant_error(formal) << "Class " << formal->get_type_decl() << " of formal parameter " << formal->get_name() << " is undefined." << endl;
        else
            object_env.addid(formal->get_name(), new Symbol(formal->get_type_decl()));
    }
    // 检查返回值
    Symbol expr_type = expr->check_type();
    if (return_type != SELF_TYPE && name_class_map.count(return_type) == 0)
        semant_error(this) << "Undefined return type " << return_type << " in method " << name << endl;
    else if (!conform(expr_type, return_type)) {
        semant_error(this) << "Inferred return type " << expr_type 
            << " of method " << name 
            << " does not conform to declared return type " << return_type << endl;
    }
    object_env.exitscope();
}

// 属性的typecheck
void attr_class::check_type() {
    Symbol expr_type = init->check_type();
    if (name == self) {
        semant_error(this) << "'self' cannot be the name of an attribute." << endl;
        exit_with_error();
    }
    if (name_class_map.count(type_decl) == 0) {
        semant_error(this) 
            << "Class " << type_decl
            << " of attribute " << name << " is undefined." << endl;
    }
    else if (name_class_map.count(type_decl) != 0 && !conform(expr_type, type_decl)) {
        semant_error(this) 
            << "Inferred type " << expr_type 
            << " of initialization of attribute " << name
            << " does not conform to declared type " << type_decl << endl;
    }
}

// expr的typecheck

Symbol assign_class::check_type() {
    Symbol expr_type = expr->check_type();

    if (object_env.lookup(name) == NULL) {
        semant_error(this) << "Assignment to undefined variable " << name << endl;
        type = expr_type;
        return type;
    }

    Symbol var_type = *object_env.lookup(name);
    if (!conform(expr_type, var_type)) {
        semant_error(this) << "Type " << expr_type << " of assignment does not conform to declared type " << var_type << endl;
        type = var_type;
        return type;
    }

    type = expr_type;
    return type;
}   

Symbol static_dispatch_class::check_type() {
    bool error = false;
    Symbol expr_type = expr->check_type();

    if (type_name != SELF_TYPE && name_class_map.count(type_name) == 0) {
        semant_error(this) << "Static dispatch to undefined class " << type_name << endl;
        type = Object;
        return type;
    }

    if (expr_type != SELF_TYPE && name_class_map.count(expr_type) == 0) {
        type = Object;
        return type;
    }

    if (!conform(expr_type, type_name)) {
        error = true;
        semant_error(this) << "Expression type " << expr_type << " does not conform to declared static dispatch type " << type_name << endl;
    }

    // 找实际使用的方法
    method_class* method = NULL;
    std::vector<Class_> inheritance_list;
    get_inheritance_list(type_name, inheritance_list);
    for (auto& it : inheritance_list) {
        Methods methods = method_table[it];
        for (auto& it2 : methods) {
            if (it2->get_name() == name) {
                method = it2;
                break;
            }
        }
    }
    if (method == NULL) {
        error = true;
        semant_error(this) << "Static dispatch to undefined method " << name << ".\n";
    }
    else {
        // 检查参数
        Formals formals = method->get_formals();
        int i = formals->first();
        int j = actual->first();
        while (formals->more(i) && actual->more(j)) {
            Symbol formal_type = formals->nth(i)->get_type_decl();
            Symbol actual_type = actual->nth(j)->check_type();
            if (!conform(actual_type, formal_type)) {
                error = true;
                semant_error(this) << "In call of method " << name << ", type " << actual_type << " of parameter " << formals->nth(i)->get_name() << " does not conform to declared type " << formal_type << ".\n";
            }
            i = formals->next(i);
            j = actual->next(j);
            if (formals->more(i) != actual->more(j)) {
                error = true;
                semant_error(this) << "Method " << name << " called with wrong number of arguments.\n";
            }
        }
    }

    if (error) {
        type = Object;
    }
    else {
        type = method->get_return_type();
        if (type == SELF_TYPE) {
            type = type_name;
        }
    }

    return type;
}

Symbol dispatch_class::check_type() {
    bool error = false;
    Symbol expr_type = expr->check_type();

    if (expr_type != SELF_TYPE && name_class_map.count(expr_type) == 0) {
        semant_error(this) << "Dispatch on undefined class " << expr_type << ".\n";
        type = Object;
        return type;
    }

    method_class* method = NULL;
    std::vector<Class_> inheritance_list;
    get_inheritance_list(expr_type, inheritance_list);
    for (auto& it : inheritance_list) {
        Methods methods = method_table[it];
        for (auto& it2 : methods) {
            if (it2->get_name() == name) {
                method = it2;
                break;
            }
        }
    }
    if (method == NULL) {
        error = true;
        semant_error(this) << "Dispatch to undefined method " << name << ".\n";
    }
    else {
        // 检查参数
        Formals formals = method->get_formals();
        int i = formals->first();
        int j = actual->first();
        while (formals->more(i) && actual->more(j)) {
            Symbol formal_type = formals->nth(i)->get_type_decl();
            Symbol actual_type = actual->nth(j)->check_type();
            if (!conform(actual_type, formal_type)) {
                error = true;
                semant_error(this) << "In call of method " << name << ", type " << actual_type << " of parameter " << formals->nth(i)->get_name() << " does not conform to declared type " << formal_type << ".\n";
            }
            i = formals->next(i);
            j = actual->next(j);
            if (formals->more(i) != actual->more(j)) {
                error = true;
                semant_error(this) << "Method " << name << " called with wrong number of arguments.\n";
            }
        }
    }

    if (error) {
        type = Object;
    }
    else {
        type = method->get_return_type();
        if (type == SELF_TYPE) {
            type = expr_type;
        }
    }

    return type;
}

// 找最近父类
static Class_ lub(Symbol name1, Symbol name2) {
    std::vector<Class_> inheritance_list1;
    get_inheritance_list(name1, inheritance_list1);
    std::vector<Class_> inheritance_list2;
    get_inheritance_list(name2, inheritance_list2);

    std::reverse(inheritance_list1.begin(), inheritance_list1.end());
    std::reverse(inheritance_list2.begin(), inheritance_list2.end());

    size_t i;
    for (i = 1; i < std::min(inheritance_list1.size(), inheritance_list2.size()); i++) {
        if (inheritance_list1[i] != inheritance_list2[i]) {
            break;
        }
    }
    return inheritance_list1[i - 1];
}

Symbol cond_class::check_type() {
    if (pred->check_type() != Bool) 
        semant_error(this) << "Predicate of cond must be boolean.\n";
    
    Symbol then_type = then_exp->check_type();
    Symbol else_type = else_exp->check_type();

    if (then_type == SELF_TYPE && else_type == SELF_TYPE) 
        type = SELF_TYPE;
    else    
        type = lub(then_type, else_type)->get_name();
    return type;
}

Symbol loop_class::check_type() {
    if (pred->check_type() != Bool)
        semant_error(this) << "Predicate of loop must be boolean.\n";
    body->check_type();
    type = Object;
    return type;
}

Symbol typcase_class::check_type() {
    Symbol expr_type = expr->check_type();

    std::set<Symbol> branch_type_decls;

    for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
        branch_class* branch = static_cast<branch_class*>(cases->nth(i));
        if (branch_type_decls.count(branch->get_type_decl()) > 0)
            semant_error(this) << "Duplicate branch type declaration " << branch->get_type_decl() << ".\n";
        else 
            branch_type_decls.insert(branch->get_type_decl());

        Symbol branch_type = branch->check_type();

        if (i == cases->first())
            type = branch_type;
        else if (type != SELF_TYPE || branch_type != SELF_TYPE)
            type = lub(type, branch_type)->get_name();
    }

    return type;
}

Symbol branch_class::check_type() {
    object_env.enterscope();
    object_env.addid(name, new Symbol(type_decl));
    type = expr->check_type();
    object_env.exitscope();
    return type;
}

Symbol block_class::check_type() {
    for (int i = body->first(); body->more(i); i = body->next(i)) {
        type = body->nth(i)->check_type();
    }
    return type;
}

Symbol let_class::check_type() {
    object_env.enterscope();
    object_env.addid(identifier, new Symbol(type_decl));

    Symbol init_type = init->check_type();
    if (name_class_map.count(init_type) == 0) 
        semant_error(this) << "Let binding " << identifier << " has type " << init_type << ", which is not a defined type.\n";
    else if (init_type != No_type && !conform(init_type, type_decl))
        semant_error(this) << "Let binding " << identifier << " has type " << init_type << ", which does not conform to declared type " << type_decl << ".\n";

    type = body->check_type();
    object_env.exitscope();
    return type;
}

Symbol plus_class::check_type() {
    Symbol type1 = e1->check_type();
    Symbol type2 = e2->check_type();
    if (type1 != Int || type2 != Int)
        semant_error(this) << "non-Int arguments: " << type1 << " + " << type2 << endl;
    type = Int;
    return type;
}

Symbol sub_class::check_type() {
    Symbol type1 = e1->check_type();
    Symbol type2 = e2->check_type();
    if (type1 != Int || type2 != Int)
        semant_error(this) << "non-Int arguments: " << type1 << " - " << type2 << endl;
    type = Int;
    return type;
}

Symbol mul_class::check_type() {
    Symbol type1 = e1->check_type();
    Symbol type2 = e2->check_type();
    if (type1 != Int || type2 != Int)
        semant_error(this) << "non-Int arguments: " << type1 << " * " << type2 << endl;
    type = Int;
    return type;
}

Symbol divide_class::check_type() {
    Symbol type1 = e1->check_type();
    Symbol type2 = e2->check_type();
    if (type1 != Int || type2 != Int)
        semant_error(this) << "non-Int arguments: " << type1 << " / " << type2 << endl;
    type = Int;
    return type;
}

Symbol neg_class::check_type() {
    type = e1->check_type();
    if (type != Int)
        semant_error(this) << "Argument of '~' has type " << type << " instead of Int.\n";
    type = Int;
    return type;
}

Symbol lt_class::check_type() {
    Symbol type1 = e1->check_type();
    Symbol type2 = e2->check_type();
    if (type1 != Int || type2 != Int)
        semant_error(this) << "non-Int arguments: " << type1 << " < " << type2 << endl;
    type = Bool;
    return type;
}

Symbol eq_class::check_type() {
    Symbol t1 = e1->check_type(), t2 = e2->check_type();
    if ((t1 == Int || t1 == Bool || t1 == Str || t2 == Int || t2 == Bool || t2 == Str) && t1 != t2)
        semant_error(this) << "Illegal comparison with a basic type.\n";
    type = Bool;
    return type;
}

Symbol leq_class::check_type() {
    Symbol type1 = e1->check_type();
    Symbol type2 = e2->check_type();
    if (type1 != Int || type2 != Int)
        semant_error(this) << "non-Int arguments: " << type1 << " <= " << type2 << endl;
    type = Bool;
    return type;
}

Symbol comp_class::check_type() {
    type = e1->check_type();
    if (type != Bool)
        semant_error(this) << "Argument of 'not' has type " << type << " instead of Bool.\n";
    type = Bool;
    return type;
}

Symbol int_const_class::check_type() {
    type = Int;
    return type;
}

Symbol bool_const_class::check_type() {
    type = Bool;
    return type;
}

Symbol string_const_class::check_type() {
    type = Str;
    return type;
}

Symbol new__class::check_type() {
    if (this->type_name != SELF_TYPE && name_class_map.count(this->type_name) == 0) {
        semant_error(this) << "'new' used with undefined class " << this->type_name << ".\n";
        this->type_name = Object;
    }
    type = this->type_name;
    return type;
}

Symbol isvoid_class::check_type() {
    e1->check_type();
    type = Bool;
    return type;
}

Symbol no_expr_class::check_type() {
    type = No_type;
    return type;
}

Symbol object_class::check_type() {
    if (name == self) {
        type = SELF_TYPE;
    } else if (object_env.lookup(name)) {
        type = *object_env.lookup(name);
    } else {
        semant_error(this) << "Undeclared identifier " << name << ".\n";
        type = Object;
    }
    return type;
}

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    install_basic_classes();
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        add_class(classes->nth(i));
    }

    /* some semantic analysis code may go here */
    check_inheritance();
    exit_with_error();

    check_main();
    exit_with_error();

    install_methods();
    exit_with_error();

    check_methods();
    exit_with_error();
}
