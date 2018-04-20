/*
 * vlab_cs_ucsb_edu_DriverProxy.cpp
 *
 *  Created on: Aug 26, 2015
 *      Author: baki
 */

#include <map>
#include <string>
#include <iostream>

#include "vlab_cs_ucsb_edu_DriverProxy.h"
#include "Driver.h"


jfieldID getHandleField(JNIEnv *env, jobject obj)
{
    jclass c = env->GetObjectClass(obj);
    // J is the type signature for long:
    return env->GetFieldID(c, "driverPointer", "J");
}

template <typename T>
T *getHandle(JNIEnv *env, jobject obj)
{
    jlong handle = env->GetLongField(obj, getHandleField(env, obj));
    return reinterpret_cast<T *>(handle);
}

template <typename T>
void setHandle(JNIEnv *env, jobject obj, T *t)
{
    jlong handle = reinterpret_cast<jlong>(t);
    env->SetLongField(obj, getHandleField(env, obj), handle);
}

jobject newBigInteger(JNIEnv *env, jstring value) {
  jclass big_integer_class = env->FindClass("java/math/BigInteger");
  jmethodID big_integer_ctor = env->GetMethodID(big_integer_class, "<init>", "(Ljava/lang/String;)V");
  jobject big_integer = env->NewObject(big_integer_class, big_integer_ctor, value);
  return big_integer;
}

void load_model_counter(JNIEnv *env, Vlab::Solver::ModelCounter& mc, jbyteArray model_counter) {
  jsize length = env->GetArrayLength(model_counter);
  jbyte* buffer = env->GetByteArrayElements(model_counter, nullptr);
  std::string bin_model_counter_str (const_cast<char*>(reinterpret_cast<char*>(buffer)), length);
  std::stringstream is (bin_model_counter_str);
  {
    cereal::BinaryInputArchive ar(is);
    mc.load(ar);
  }
  env->ReleaseByteArrayElements(model_counter, buffer, JNI_ABORT);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    initABC
 * Signature: (I)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_initABC (JNIEnv *env, jobject obj, jint log_level) {

  Vlab::Driver *abc_driver = new Vlab::Driver();
  abc_driver->InitializeLogger((int)log_level);
  setHandle(env, obj, abc_driver);
}


/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    setOption
 * Signature: (I)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_setOption__I
  (JNIEnv *env, jobject obj, jint option) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  abc_driver->set_option(static_cast<Vlab::Option::Name>(option));
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    setOption
 * Signature: (II)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_setOption__II
  (JNIEnv *env, jobject obj, jint option, jint value) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  abc_driver->set_option(static_cast<Vlab::Option::Name>(option), value);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    setOption
 * Signature: (ILjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_setOption__ILjava_lang_String_2
  (JNIEnv *env, jobject obj, jint option, jstring value) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  const char* value_arr = env->GetStringUTFChars(value, JNI_FALSE);
  std::string value_str {value_arr};
  abc_driver->set_option(static_cast<Vlab::Option::Name>(option), value_str);
  env->ReleaseStringUTFChars(value, value_arr);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    isSatisfiable
 * Signature: (Ljava/lang/String;)Z
 */
JNIEXPORT jboolean JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_isSatisfiable
  (JNIEnv *env, jobject obj, jstring constraint) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  std::istringstream input_constraint;
  const char* constraint_str = env->GetStringUTFChars(constraint, JNI_FALSE);
  input_constraint.str(constraint_str);
  abc_driver->reset();
  abc_driver->Parse(&input_constraint);
  env->ReleaseStringUTFChars(constraint, constraint_str);
  abc_driver->InitializeSolver();
  abc_driver->Solve();
  bool result = abc_driver->is_sat();
  return (jboolean)result;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    isSatisfiable
 * Signature: (Ljava/lang/StringLjava/lang/String;)Z
 */
JNIEXPORT jboolean JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_isSatisfiable2
  (JNIEnv *env, jobject obj, jstring constraint, jboolean branch) {

	Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
	std::istringstream input_constraint;
	const char* constraint_str = env->GetStringUTFChars(constraint, JNI_FALSE);
	input_constraint.str(constraint_str);

  if(branch) {
    abc_driver->saveStateAndBranch();
  }
	abc_driver->Parse(&input_constraint);
	env->ReleaseStringUTFChars(constraint, constraint_str);
	abc_driver->InitializeSolver();
	abc_driver->Solve();
	bool result = abc_driver->is_sat();
	return (jboolean)result;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    loadID
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_loadID
  (JNIEnv *env, jobject obj, jstring id) {
	Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
	const char* id_arr = env->GetStringUTFChars(id, JNI_FALSE);
	std::string id_str {id_arr};
	abc_driver->loadID(id_str);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    getCurrentID
 * Signature: ()V
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_getCurrentID
  (JNIEnv *env, jobject obj) {
	Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
	std::string id = abc_driver->getCurrentID();
	jstring j_id = env->NewStringUTF(id.c_str());
	return j_id;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    destroyID
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_destroyID
  (JNIEnv *env, jobject obj, jstring id) {
	Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
	const char* id_arr = env->GetStringUTFChars(id, JNI_FALSE);
	std::string id_str {id_arr};
	abc_driver->destroyID(id_str);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    countVariable
 * Signature: (Ljava/lang/String;J)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_countVariable__Ljava_lang_String_2J
  (JNIEnv *env, jobject obj, jstring var_name, jlong bound) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  const char* var_name_arr = env->GetStringUTFChars(var_name, JNI_FALSE);
  std::string var_name_str {var_name_arr};
  auto result = abc_driver->CountVariable(var_name_str, bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  env->ReleaseStringUTFChars(var_name, var_name_arr);
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    countInts
 * Signature: (J)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_countInts__J
  (JNIEnv *env, jobject obj, jlong bound) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  auto result = abc_driver->CountInts(bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    countStrs
 * Signature: (J)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_countStrs__J
  (JNIEnv *env, jobject obj, jlong bound) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  auto result = abc_driver->CountStrs(bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    count
 * Signature: (JJ)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_count__JJ
  (JNIEnv *env, jobject obj, jlong int_bound, jlong str_bound) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  auto result = abc_driver->Count(int_bound, str_bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    getModelCounterForVariable
 * Signature: (Ljava/lang/String;)[B
 */
JNIEXPORT jbyteArray JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_getModelCounterForVariable
  (JNIEnv *env, jobject obj, jstring var_name) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  const char* var_name_arr = env->GetStringUTFChars(var_name, JNI_FALSE);
  std::string var_name_str {var_name_arr};
  auto mc = abc_driver->GetModelCounterForVariable(var_name_str);
  std::stringstream os;
  {
    cereal::BinaryOutputArchive ar(os);
    mc.save(ar);
  }
  env->ReleaseStringUTFChars(var_name, var_name_arr);
  std::string bin_mc = os.str();
  jbyteArray array = env->NewByteArray (bin_mc.size());
  env->SetByteArrayRegion (array, 0, bin_mc.size(), reinterpret_cast<jbyte*>(const_cast<char*>(bin_mc.c_str())));
  return array;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    getModelCounter
 * Signature: ()[B
 */
JNIEXPORT jbyteArray JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_getModelCounter
  (JNIEnv *env, jobject obj) {

  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  auto mc = abc_driver->GetModelCounter();
  std::stringstream os;
  {
    cereal::BinaryOutputArchive ar(os);
    mc.save(ar);
  }
  std::string bin_mc = os.str();
  jbyteArray array = env->NewByteArray (bin_mc.size());
  env->SetByteArrayRegion (array, 0, bin_mc.size(), reinterpret_cast<jbyte*>(const_cast<char*>(bin_mc.c_str())));
  return array;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    countVariable
 * Signature: (Ljava/lang/String;J[B)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_countVariable__Ljava_lang_String_2J_3B
  (JNIEnv *env, jobject obj, jstring var_name, jlong bound, jbyteArray model_counter) {

  Vlab::Solver::ModelCounter mc;
  load_model_counter(env, mc, model_counter);
  auto result = mc.Count(bound, bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    countInts
 * Signature: (J[B)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_countInts__J_3B
  (JNIEnv *env, jobject obj, jlong bound, jbyteArray model_counter) {

  Vlab::Solver::ModelCounter mc;
  load_model_counter(env, mc, model_counter);
  auto result = mc.CountInts(bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    countStrs
 * Signature: (J[B)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_countStrs__J_3B
  (JNIEnv *env, jobject obj, jlong bound, jbyteArray model_counter) {

  Vlab::Solver::ModelCounter mc;
  load_model_counter(env, mc, model_counter);
  auto result = mc.CountStrs(bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    count
 * Signature: (JJ[B)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_count__JJ_3B
  (JNIEnv *env, jobject obj, jlong int_bound, jlong str_bound, jbyteArray model_counter) {

  Vlab::Solver::ModelCounter mc;
  load_model_counter(env, mc, model_counter);
  auto result = mc.Count(int_bound, str_bound);
  std::stringstream ss;
  ss << result;
  jstring result_string = env->NewStringUTF(ss.str().c_str());
  return newBigInteger(env, result_string);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    printResultAutomaton
 * Signature: ()V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_printResultAutomaton__ (JNIEnv *env, jobject obj) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  if (abc_driver->is_sat()) {
    int index = 0;
    for(auto& variable_entry : abc_driver->getSatisfyingVariables()) {
      abc_driver->printResult(variable_entry.second, std::cout);
    }
    std::cout.flush();
  }
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    printResultAutomaton
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_printResultAutomaton__Ljava_lang_String_2 (JNIEnv *env, jobject obj, jstring filePath) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  const char* file_path_str = env->GetStringUTFChars(filePath, JNI_FALSE);
  std::string file_path {file_path_str};

  if (abc_driver->is_sat()) {
    int index = 0;
    for(auto& variable_entry : abc_driver->getSatisfyingVariables()) {
      std::stringstream ss;
      ss << file_path << "_" << index << ".dot";
      abc_driver->inspectResult(variable_entry.second, ss.str());
    }
    std::cout.flush();
  }
  env->ReleaseStringUTFChars(filePath, file_path_str);
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    getSatisfyingExamples
 * Signature: ()Ljava/util/Map;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_getSatisfyingExamples (JNIEnv *env, jobject obj) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  jclass hashMapClass = env->FindClass("java/util/HashMap");
  jmethodID hashMapCtor = env->GetMethodID(hashMapClass, "<init>", "()V");
  jobject map = env->NewObject(hashMapClass, hashMapCtor);

  std::map<std::string, std::string> results = abc_driver->getSatisfyingExamples();

  jmethodID hasMapPut = env->GetMethodID(hashMapClass, "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

  for (auto var_entry : results) {
    jstring var_name = env->NewStringUTF(var_entry.first.c_str());
    jstring var_value = env->NewStringUTF(var_entry.second.c_str());
    env->CallObjectMethod(map, hasMapPut, var_name, var_value);
  }

  return map;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    getSatisfyingExamplesRandom
 * Signature: ()Ljava/util/Map;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_getSatisfyingExamplesRandom (JNIEnv *env, jobject obj) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  jclass hashMapClass = env->FindClass("java/util/HashMap");
  jmethodID hashMapCtor = env->GetMethodID(hashMapClass, "<init>", "()V");
  jobject map = env->NewObject(hashMapClass, hashMapCtor);

  std::map<std::string, std::string> results = abc_driver->getSatisfyingExamplesRandom();

  jmethodID hasMapPut = env->GetMethodID(hashMapClass, "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

  for (auto var_entry : results) {
    jstring var_name = env->NewStringUTF(var_entry.first.c_str());
    jstring var_value = env->NewStringUTF(var_entry.second.c_str());
    env->CallObjectMethod(map, hasMapPut, var_name, var_value);
  }

  return map;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    getSatisfyingExamplesRandomBounded
 * Signature: (I)Ljava/util/Map;
 */
JNIEXPORT jobject JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_getSatisfyingExamplesRandomBounded (JNIEnv *env, jobject obj, jint bound) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  jclass hashMapClass = env->FindClass("java/util/HashMap");
  jmethodID hashMapCtor = env->GetMethodID(hashMapClass, "<init>", "()V");
  jobject map = env->NewObject(hashMapClass, hashMapCtor);

  std::map<std::string, std::string> results = abc_driver->getSatisfyingExamplesRandomBounded((int)bound);

  jmethodID hasMapPut = env->GetMethodID(hashMapClass, "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

  for (auto var_entry : results) {
    jstring var_name = env->NewStringUTF(var_entry.first.c_str());
    jstring var_value = env->NewStringUTF(var_entry.second.c_str());
    env->CallObjectMethod(map, hasMapPut, var_name, var_value);
  }

  return map;
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    reset
 * Signature: ()V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_reset (JNIEnv *env, jobject obj) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  abc_driver->reset();
}

/*
 * Class:     vlab_cs_ucsb_edu_DriverProxy
 * Method:    dispose
 * Signature: ()V
 */
JNIEXPORT void JNICALL Java_vlab_cs_ucsb_edu_DriverProxy_dispose (JNIEnv *env, jobject obj) {
  Vlab::Driver *abc_driver = getHandle<Vlab::Driver>(env, obj);
  Vlab::Driver *tmp = abc_driver;
  abc_driver = nullptr;
  setHandle(env, obj, abc_driver);
  delete tmp;
}
