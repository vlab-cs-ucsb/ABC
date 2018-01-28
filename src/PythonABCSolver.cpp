/*
 * vlab_cs_ucsb_edu_DriverProxy.cpp
 *
 *  Created on: Aug 26, 2015
 *      Author: baki
 */

#include <map>
#include <string>
#include <iostream>

#include "PythonABCSolver.h"
#include "Driver.h"

extern "C"
{
#include <structmember.h>
    
typedef struct 
{
    PyObject_HEAD
    PyObject *driver_handle;
} DriverProxy;

static void DriverProxy_dealloc(DriverProxy* self)
{
    Py_XDECREF(self->driver_handle);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

static PyObject* 
DriverProxy_new(PyTypeObject* type, PyObject* args, PyObject* kwds)
{
    DriverProxy* self = NULL;
    self = (DriverProxy*)type->tp_alloc(type, 0);
    if (self != NULL)
    {
        self->driver_handle = Py_None;
        Py_INCREF(Py_None);
    }
    return (PyObject*)self;
}

static void VlabDriver_PyCapsule_Destructor(PyObject* capsule)
{
    Vlab::Driver* driver = (Vlab::Driver*) PyCapsule_GetPointer(capsule, "driver_handle");
    delete driver;
}

static int DriverProxy_init (DriverProxy* self, PyObject* args, PyObject* kwargs)
{
    int log_level = 0;

    if(!PyArg_ParseTuple(args, "i", &log_level))
    {
        return -1;
    }

    Vlab::Driver *abc_driver = new Vlab::Driver();
    abc_driver->InitializeLogger((int)log_level);

    PyObject* capsule = PyCapsule_New(abc_driver, "driver_handle", VlabDriver_PyCapsule_Destructor);
    if (capsule == NULL)
    {
        delete abc_driver;
        return -1;
    }
    
    PyObject* tmp = self->driver_handle;
    self->driver_handle = capsule;
    Py_XDECREF(tmp);

    return 0;
}

static PyMemberDef driverProxyMembers[] = {
    {"driver_handle", T_OBJECT_EX, offsetof(DriverProxy, driver_handle), 0, "Opaque handle of the ABC String solver driver object."},
    {NULL},
};


static Vlab::Driver *getDriverHandle(DriverProxy* self)
{
	PyObject* capsule = self->driver_handle;
	if (capsule == NULL)
	{
		PyErr_SetString(PyExc_AttributeError, "driver_handle was set to NULL, what the fuck happened");
		return NULL;
	}
    void* ptr = PyCapsule_GetPointer(capsule, "driver_handle");
    if (ptr == NULL)
    {
        PyErr_SetString(PyExc_RuntimeError, "Retrieving pointer from capsule failed!");
    }
    return reinterpret_cast<Vlab::Driver *>(ptr);
}

static int setDriverHandle(DriverProxy* self, Vlab::Driver *driver)
{
    void* ptr = reinterpret_cast<void*>(driver);
    PyObject* capsule = PyCapsule_New(ptr, NULL, VlabDriver_PyCapsule_Destructor);
    if (capsule == NULL)
    {
        PyErr_SetString(PyExc_RuntimeError, "Could not create capsule for Vlab::Driver");
        return 0;
    }
    Py_DECREF(self->driver_handle);
    self->driver_handle = capsule;
    return 1;
}


static PyObject* newBigInteger(const char* value) {
    PyObject* int_object = PyLong_FromString((char*)value, NULL, 10);
    return int_object;
}

static void load_model_counter(Vlab::Solver::ModelCounter& mc, PyObject* model_counter)
{
    Py_ssize_t length = PyByteArray_Size(model_counter);
    char* buffer = PyByteArray_AsString(model_counter);
    std::string bin_model_counter_str (const_cast<char*>(reinterpret_cast<char*>(buffer)), length);
    std::stringstream is (bin_model_counter_str);
    {
        cereal::BinaryInputArchive ar(is);
        mc.load(ar);
    }
}


PyObject* DriverProxy_setOption__Int (DriverProxy* self, PyObject* args)
{
    int option = 0;

    if(!PyArg_ParseTuple(args, "i", &option))
    {
        return NULL;
    }

    Vlab::Driver *abc_driver = getDriverHandle(self);
    abc_driver->set_option(static_cast<Vlab::Option::Name>(option));
    return Py_BuildValue("");
}

PyObject* DriverProxy_setOption__IntInt  (DriverProxy* self, PyObject* args)
{
    int option = 0;
    int value = 0;

    if(!PyArg_ParseTuple(args, "ii", &option, &value))
    {
        return NULL;
    }

    Vlab::Driver *abc_driver = getDriverHandle(self);
    abc_driver->set_option(static_cast<Vlab::Option::Name>(option), value);
    return Py_BuildValue("");
}

PyObject* DriverProxy_setOption__IntString(DriverProxy* self, PyObject* args)
{
    const char* value_str = NULL;
    int option = 0;

    if(!PyArg_ParseTuple(args, "is", &option, &value_str))
    {
        return NULL;
    }

    Vlab::Driver *abc_driver = getDriverHandle(self);
    abc_driver->set_option(static_cast<Vlab::Option::Name>(option), value_str);
    return Py_BuildValue("");
}

PyObject* DriverProxy_isSatisfiable(DriverProxy* self, PyObject* args)
{
    const char* constraint_str = NULL;

    if(!PyArg_ParseTuple(args, "s", &constraint_str))
        { return NULL; }

    std::istringstream input_constraint;
    input_constraint.str(constraint_str);

    Vlab::Driver *abc_driver = getDriverHandle(self);
    abc_driver->reset();
    abc_driver->Parse(&input_constraint);
    abc_driver->InitializeSolver();
    abc_driver->Solve();
    bool result = abc_driver->is_sat();
    PyObject* p_result = result ? Py_True : Py_False;
    Py_XINCREF(p_result);
    return p_result;
}

PyObject* DriverProxy_countVariable__StringLong(DriverProxy* self, PyObject* args)
{
    const char* constraint_str = NULL;
    const unsigned long bound = 0;
    if(!PyArg_ParseTuple(args, "sk", &constraint_str, &bound))
        { return NULL; }

    std::string var_name_str {constraint_str};

    Vlab::Driver *abc_driver = getDriverHandle(self);
    auto result = abc_driver->CountVariable(var_name_str, bound);

    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_countInts__Long(DriverProxy* self, PyObject* args)
{
    const unsigned long bound = 0;
    if (!PyArg_ParseTuple(args, "k", &bound))
        { return NULL; }

    Vlab::Driver *abc_driver = getDriverHandle(self);
    auto result = abc_driver->CountInts(bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_countStrs__Long(DriverProxy* self, PyObject* args)
{
    const unsigned long bound = 0;
    if (!PyArg_ParseTuple(args, "k", &bound))
        { return NULL; }

    Vlab::Driver *abc_driver = getDriverHandle(self);
    auto result = abc_driver->CountStrs(bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_count__LongLong(DriverProxy* self, PyObject* args)
{
    const unsigned long int_bound = 0;
    const unsigned long str_bound = 0;
    if (!PyArg_ParseTuple(args, "kk", &int_bound, &str_bound))
        { return NULL; }

    Vlab::Driver *abc_driver = getDriverHandle(self);
    auto result = abc_driver->Count(int_bound, str_bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_getModelCounterForVariable_String(DriverProxy* self, PyObject* args)
{
    const char* var_name = NULL;
    if (!PyArg_ParseTuple(args, "s", &var_name))
        { return NULL; }

    std::string var_name_str {var_name};


    Vlab::Driver *abc_driver = getDriverHandle(self);
    auto mc = abc_driver->GetModelCounterForVariable(var_name_str);

    std::stringstream os;
    {
        cereal::BinaryOutputArchive ar(os);
        mc.save(ar);
    }

    std::string bin_mc = os.str();
    PyObject* byte_array = PyByteArray_FromStringAndSize(bin_mc.c_str(), bin_mc.size());
    return byte_array;
}

static PyObject* DriverProxy_getModelCounter(DriverProxy* self, PyObject* args)
{
    Vlab::Driver *abc_driver = getDriverHandle(self);
    auto mc = abc_driver->GetModelCounter();

    std::stringstream os;
    {
        cereal::BinaryOutputArchive ar(os);
        mc.save(ar);
    }

    std::string bin_mc = os.str();
    PyObject* byte_array = PyByteArray_FromStringAndSize(bin_mc.c_str(), bin_mc.size());

    return byte_array;
}

static PyObject* DriverProxy_countVariable_StringLongBytearray(DriverProxy* self, PyObject* args)
{
    char* var_name = NULL;
    const unsigned long bound = 0;
    PyObject* model_counter = NULL;
    if (!PyArg_ParseTuple(args, "skO!", &var_name, &bound, &PyByteArray_Type, &model_counter))
        { return NULL; }

    Vlab::Solver::ModelCounter mc;
    load_model_counter(mc, model_counter);
    auto result = mc.Count(bound, bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_countInts_LongBytearray(DriverProxy* self, PyObject* args)
{
    const unsigned long bound = 0;
    PyObject* model_counter = NULL;
    if (!PyArg_ParseTuple(args, "kO!", &bound, &PyByteArray_Type, &model_counter))
        { return NULL; }

    Vlab::Solver::ModelCounter mc;
    load_model_counter(mc, model_counter);
    auto result = mc.CountInts(bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_countStrs_LongBytearray(DriverProxy* self, PyObject* args)
{
    const unsigned long bound = 0;
    PyObject* model_counter = NULL;
    if (!PyArg_ParseTuple(args, "kO!", &bound, &PyByteArray_Type, &model_counter))
        { return NULL; }

    Vlab::Solver::ModelCounter mc;
    load_model_counter(mc, model_counter);
    auto result = mc.CountStrs(bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_count_LongLongBytearray(DriverProxy* self, PyObject* args)
{
    const unsigned long int_bound = 0;
    const unsigned long str_bound = 0;
    PyObject* model_counter = NULL;
    if (!PyArg_ParseTuple(args, "kkO!", &int_bound, &str_bound, &PyByteArray_Type, &model_counter))
        { return NULL; }

    Vlab::Solver::ModelCounter mc;
    load_model_counter(mc, model_counter);
    auto result = mc.Count(int_bound, str_bound);
    std::stringstream ss;
    ss << result;
    return newBigInteger(ss.str().c_str());
}

static PyObject* DriverProxy_printResultAutomaton(DriverProxy* self, PyObject* args)
{
    Vlab::Driver *abc_driver = getDriverHandle(self);
    if (abc_driver->is_sat())
    {
        for(auto& variable_entry : abc_driver->getSatisfyingVariables())
        {
            abc_driver->printResult(variable_entry.second, std::cout);
        }
        std::cout.flush();
    }
    return Py_BuildValue("");
}

static PyObject* DriverProxy_printResultAutomaton_String(DriverProxy* self, PyObject* args)
{
    const char* file_path = NULL;
    if(!PyArg_ParseTuple(args, "s", &file_path))
    {
        return NULL;
    }

    std::string file_path_str {file_path};
    Vlab::Driver *abc_driver = getDriverHandle(self);
    if (abc_driver->is_sat())
    {
        int index = 0;
        for(auto& variable_entry : abc_driver->getSatisfyingVariables())
        {
            std::stringstream ss;
            ss << file_path << "_" << index << ".dot";
            abc_driver->inspectResult(variable_entry.second, ss.str());
        }
        std::cout.flush();
    }
    return Py_BuildValue("");
}

static PyObject* DriverProxy_getSatisfyingExamples(DriverProxy* self, PyObject* args)
{
    PyObject* map = PyDict_New();
    if (map == NULL)
    {
        return NULL;
    }
    // TODO handle ref counting for this case
    Vlab::Driver *abc_driver = getDriverHandle(self);
    std::map<std::string, std::string> results = abc_driver->getSatisfyingExamples();
    for (auto var_entry : results)
    {
        PyObject* var_name = PyString_FromString(var_entry.first.c_str());
        PyObject* var_value = PyString_FromString(var_entry.second.c_str());
        PyDict_SetItem(map, var_name, var_value);
    }
    return map;
}

static PyObject* DriverProxy_reset(DriverProxy* self, PyObject* args)
{
    Vlab::Driver *abc_driver = getDriverHandle(self);
    abc_driver->reset();
    return Py_BuildValue("");
}

/*PyObject* DriverProxy_dispose(DriverProxy* self, PyObject* args)
{
    Vlab::Driver *abc_driver = getDriverHandle(self);
    Vlab::Driver *tmp = abc_driver;
    abc_driver = nullptr;
    setDriverHandle(self, abc_driver);
    delete tmp;
    return Py_BuildValue("");
}*/


static PyMethodDef driverProxyMethods[] = {
    {"setOption__Int", (PyCFunction)DriverProxy_setOption__Int, METH_VARARGS | METH_KEYWORDS, "set a boolean option"},
    {"setOption__IntInt", (PyCFunction)DriverProxy_setOption__IntInt, METH_VARARGS | METH_KEYWORDS, "set an integer option"},
    {"setOption__IntString", (PyCFunction)DriverProxy_setOption__IntString, METH_VARARGS | METH_KEYWORDS, "set a string option"},
    {"isSatisfiable", (PyCFunction)DriverProxy_isSatisfiable, METH_VARARGS | METH_KEYWORDS, "determine satisfiability of the constraints"},
    {"countVariable__StringLong", (PyCFunction)DriverProxy_countVariable__StringLong, METH_VARARGS | METH_KEYWORDS, "count the solutions for a variable"},
    {"countInts__Long", (PyCFunction)DriverProxy_countInts__Long, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"countStrs__Long", (PyCFunction)DriverProxy_countStrs__Long, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"count__LongLong", (PyCFunction)DriverProxy_count__LongLong, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"getModelCounterForVariable_String", (PyCFunction)DriverProxy_getModelCounterForVariable_String, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"getModelCounter", (PyCFunction)DriverProxy_getModelCounter, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"countVariable_StringLongBytearray", (PyCFunction)DriverProxy_countVariable_StringLongBytearray, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"countInts_LongBytearray", (PyCFunction)DriverProxy_countInts_LongBytearray, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"countStrs_LongBytearray", (PyCFunction)DriverProxy_countStrs_LongBytearray, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"count_LongLongBytearray", (PyCFunction)DriverProxy_count_LongLongBytearray, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"printResultAutomaton", (PyCFunction)DriverProxy_printResultAutomaton, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"printResultAutomaton_String", (PyCFunction)DriverProxy_printResultAutomaton_String, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"getSatisfyingExamples", (PyCFunction)DriverProxy_getSatisfyingExamples, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {"reset", (PyCFunction)DriverProxy_reset, METH_VARARGS | METH_KEYWORDS, "<unknown>"},
    {NULL},
};

static PyTypeObject DriverProxyType {
    PyVarObject_HEAD_INIT(NULL, 0)
    "PythonABCSolver.DriverProxy",   //  tp_name
    sizeof(DriverProxy),    // tp_basicsize
    0,  // tp_itemsize
    (destructor)DriverProxy_dealloc,    // tp_dealloc
    0,  //  tp_print
    0,  //  tp_getattr
    0,  //  tp_setattr
    0,  //  tp_compare
    0,  //  tp_repr
    0,  //  tp_as_number
    0,  //  tp_as_sequence
    0,  //  tp_as_mapping
    0,  //  tp_hash
    0,  //  tp_call
    0,  //  tp_str
    0,  //  tp_getattro
    0,  //  tp_setattro
    0,  //  tp_as_buffer
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,   //  tp_flags
    "Python Driver Proxy object to interact with the ABC string solver",    //  tp_doc
    0,  //  tp_traverse
    0,  //  tp_clear
    0,  //  tp_richcompare
    0,  //  tp_weaklistoffset
    0,  //  tp_iter
    0,  //  tp_iternext
    driverProxyMethods,    //  tp_methods
    driverProxyMembers,    //  tp_members
    0,  //  tp_getset
    0,  //  tp_base
    0,  //  tp_dict
    0,  //  tp_descr_get
    0,  //  tp_descr_set
    0,  //  tp_dictoffset
    (initproc)DriverProxy_init, //  tp_init
    0,  //  tp_alloc
    DriverProxy_new,    //  tp_new
};


static PyMethodDef moduleMethods[] = { 
    {NULL}, // SENTINEL
};

#ifndef PyMODINIT_FUNC
#define PyMODINIT_FUNC void
#endif

PyMODINIT_FUNC
initPythonABCSolver(void)
{
    // https://www.safaribooksonline.com/library/view/python-cookbook/0596001673/ch16s06.html
    if (PyType_Ready(&DriverProxyType) < 0)
    {
        return;
    }

    PyObject* module = Py_InitModule3("PythonABCSolver", moduleMethods, "Module to allow interaction with the ABC string solver.");
    if (module == NULL)
    {
        return;
    }
    Py_INCREF(&DriverProxyType);
    PyModule_AddObject(module, "DriverProxy", (PyObject*)&DriverProxyType);
}

}
