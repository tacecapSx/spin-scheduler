// Max Heap

// Heap structure
typedef Heap {
  byte data[MAX_TASKS];
  int size;
  int insertion_counter;
};

// Global heap instance
Heap heap;

// Initialize the heap
inline heap_init() {
  heap.size = 0;
}

// Swap helper function - assigning fields individually
inline swap(i, j) {
  d_step {
    byte temp = heap.data[i];
    heap.data[i] = heap.data[j];
    heap.data[j] = temp;
  }
}

// Restore heap property upwards
inline bubble_up(_index) {
  int index = _index;
  int parent;
  
  do
  :: index > 0 -> 
    parent = (index - 1) / 2;

    if
    :: (task_data[heap.data[index]].p < task_data[heap.data[parent]].p) ||
       (task_data[heap.data[index]].p == task_data[heap.data[parent]].p &&
        task_data[heap.data[index]].insertion_order > task_data[heap.data[parent]].insertion_order) ->
        break
    :: else ->
        swap(index, parent);
        index = parent;
    fi;
  :: else -> break
  od;
}


// Restore heap property downwards
inline bubble_down(_index) {
  int index = _index;
  int left, right, largest;

  do
  :: index < heap.size ->
    d_step {
      left = 2 * index + 1;
      right = 2 * index + 2;
      largest = index;
    }

    if
    :: left < heap.size ->
        if
        :: (task_data[heap.data[left]].p > task_data[heap.data[largest]].p) ||
           (task_data[heap.data[left]].p == task_data[heap.data[largest]].p &&
           task_data[heap.data[left]].insertion_order < task_data[heap.data[largest]].insertion_order) ->
            largest = left;
        :: else -> skip
        fi;
    :: else -> skip
    fi;

    if
    :: right < heap.size ->
        if
        :: (task_data[heap.data[right]].p > task_data[heap.data[largest]].p) ||
           (task_data[heap.data[right]].p == task_data[heap.data[largest]].p &&
           task_data[heap.data[right]].insertion_order < task_data[heap.data[largest]].insertion_order) ->
            largest = right;
        :: else -> skip
        fi;
    :: else -> skip
    fi;

    if
    :: largest == index -> break;
    :: else ->
        swap(index, largest);
        index = largest;
    fi;
  :: else -> break
  od;
}

// Insert an element into the heap - assigning fields individually
inline heap_insert(task_index) {
  // If heap.size == MAX_TASKS, then there is overflow: attempted insert when heap is full
  atomic {
    task_data[task_index].insertion_order = heap.insertion_counter;
    heap.insertion_counter++;
    
    heap.data[heap.size] = task_index;
    
    bubble_up(heap.size);
    heap.size++;
  }
}

// Get the maximum priority element
inline heap_get_max(result) {
  atomic { 
    // If heap.size == 0, then there is underflow: no elements to extract
    // Copy heap.data[0] to result
    result = heap.data[0];
    
    heap.size--;
    
    heap.data[0] = heap.data[heap.size];
    
    bubble_down(0);
  }
}