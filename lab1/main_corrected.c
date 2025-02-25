#include "pico/stdlib.h"
/* !!! PART 2 & 3 !!! */
#include "pico/util/queue.h"
#include "hardware/pwm.h"

/* !!! MIGHT WANT TO CHANGE THIS !!! */
#define BUTTON_DEBOUNCE_DELAY 50
#define EVENT_QUEUE_LENGTH    10

#define STATE_0_DELAY 500
#define STATE_1_DELAY 500
#define STATE_2_DELAY 250
#define STATE_3_DELAY 20

#define BRIGHTNESS_STEP 10

/* Function pointer primitive */ 
typedef void (*state_func_t)(void);

typedef struct _state_t {
    uint8_t id;
    state_func_t Enter;
    state_func_t Do;
    state_func_t Exit;
    uint32_t delay_ms;
} state_t;

typedef enum _event_t {
    b1_evt = 0,
    b2_evt = 1,
    b3_evt = 2,
    no_evt = 3
} event_t;

const static uint LED[4] = {0, 1, 2, 3};
const uint n_LED = sizeof(LED) / sizeof(LED[0]);

const static uint B[3] = {20, 21, 22};
const uint n_B = sizeof(B) / sizeof(B[0]);

/* !!! PART 2 & 3 !!! */
/* Define event queue */
queue_t event_queue;
unsigned long button_time = 0;

void button_isr(uint gpio, uint32_t events) {
    /* !!! PART 2 !!! */
    if ((to_ms_since_boot(get_absolute_time()) - button_time) > BUTTON_DEBOUNCE_DELAY) {
        button_time = to_ms_since_boot(get_absolute_time());
        event_t evt;

        switch (gpio) {
            case B[0]: 
                evt = b1_evt;
                break; 
            case B[1]: 
                evt = b2_evt;
                break;
            case B[2]:
                evt = b3_evt;
                break;
            default:
                return;
        }
        queue_try_add(&event_queue, &evt);
    }
}

void private_init() {
    /* !!! PART 2 !!! */
    /* Event queue setup */ 
    queue_init(&event_queue, sizeof(event_t), EVENT_QUEUE_LENGTH); 

    /* !!! PART 2 !!! */
    /* Button setup */
    for (int i = 0; i < n_B; i++) {
        gpio_init(B[i]);
        gpio_set_dir(B[i], GPIO_IN);
        gpio_pull_up(B[i]);
        gpio_set_irq_enabled_with_callback(B[i], GPIO_IRQ_EDGE_FALL, true, button_isr);
    }

    /* !!! PART 1 !!! */
    /* LED setup */
    for (int i = 0; i < n_LED; i++) {
        gpio_init(LED[i]);
        gpio_set_dir(LED[i], GPIO_OUT);
        gpio_put(LED[i], 0);
    }
}

/* The next three methods are for convenience, you might want to use them. */
event_t get_event(void) {
    /* !!!! PART 2 !!!! */
    event_t evt = no_evt;
    if (queue_try_remove(&event_queue, &evt)) return evt;
    return no_evt; 
}

void leds_off() {
    /* !!! PART 1 !!! */
    for (int i = 0; i < n_LED; i++) gpio_put(LED[i], 0);
}

void leds_on() {
    /* !!! PART 2 !!! */
    for (int i = 0; i < n_LED; i++) gpio_put(LED[i], 1);
}

void enter_state_0(void) {
    leds_off();
}
void do_state_0(void) {
    static uint current_led = 0;
    leds_off();
    gpio_put(LED[current_led], 1);
    current_led = (current_led + 1) % n_LED;
}
void exit_state_0(void) {
    leds_off();
}

void enter_state_1(void) {
    leds_off();
}
void do_state_1(void) {
    static bool on = false;
    if (on) leds_off();
    else leds_on();
    on = !on;
}
void exit_state_1(void) {
    leds_off();
}

void enter_state_2(void) {
    leds_off();
}
void do_state_2(void) {
    static int8_t current_led = n_LED - 1;
    leds_off();
    gpio_put(current_led, 1);
    current_led = (current_led - 1 + n_LED) % n_LED;
}
void exit_state_2(void) {
    leds_off();
}

void enter_state_3(void) {
    leds_off();

    gpio_set_function(LED[0], GPIO_FUNC_PWM);
    uint slice_num = pwm_gpio_to_slice_num(LED[0]);
    pwm_set_wrap(slice_num, 255);
    pwm_set_gpio_level(LED[0], 0);
    pwm_set_enabled(slice_num, 1);
}
void do_state_3(void) {
    static uint bright = 0;
    static bool incr = true;

    pwm_set_gpio_level(LED[0], bright);

    if (incr) {
        bright += BRIGHTNESS_STEP;
        if (bright >= 255) incr = false;
    } else {
        bright -= BRIGHTNESS_STEP;
        if (bright <= 0) incr = true;
    }
}
void exit_state_3(void) {
    pwm_set_enabled(pwm_gpio_to_slice_num(LED[0]), 0);
    gpio_set_function(LED[0], GPIO_FUNC_SIO);

    leds_off();
}

/* !!! PART 1 !!! */
const state_t state0 = {0, enter_state_0, do_state_0, exit_state_0, STATE_0_DELAY};
const state_t state1 = {1, enter_state_1, do_state_1, exit_state_1, STATE_1_DELAY};
const state_t state2 = {2, enter_state_2, do_state_2, exit_state_2, STATE_2_DELAY};
const state_t state3 = {3, enter_state_3, do_state_3, exit_state_3, STATE_3_DELAY};

/* !!! PART 2 !!! */
// const state_t state_table[][] = {};
const state_t state_table[4][4] = {
    {state0, state2, state1, state3},
    {state0, state1, state2, state3},
    {state1, state0, state2, state3},
    {state0, state0, state0, state0}
};

/* !!! ALL PARTS !!! */
int main() {
    private_init(); 

    state_t current_state = state0;
    event_t evt = no_evt;

    current_state.Enter();  // Correct usage: use dot operator on current_state.
    while (1) {
        current_state.Do();  // Correct usage: use dot operator on current_state.
        sleep_ms(current_state.delay_ms);
        evt = get_event();
    
        if (evt != no_evt) {
            current_state.Exit();  // Correct usage: use dot operator on current_state.
            current_state = state_table[current_state.id][evt];
            current_state.Enter();  // Correct usage: use dot operator on current_state.
        }
    }
}