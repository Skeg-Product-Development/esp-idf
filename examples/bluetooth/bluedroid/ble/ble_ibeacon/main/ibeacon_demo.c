/*
   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/



/****************************************************************************
*
* This file is for iBeacon demo. It supports both iBeacon sender and receiver
* which is distinguished by macros IBEACON_SENDER and IBEACON_RECEIVER,
*
* iBeacon is a trademark of Apple Inc. Before building devices which use iBeacon technology,
* visit https://developer.apple.com/ibeacon/ to obtain a license.
*
****************************************************************************/

#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <stdio.h>
#include "nvs_flash.h"

#include "esp_bt.h"
#include "esp_gap_ble_api.h"
#include "esp_gattc_api.h"
#include "esp_gatt_defs.h"
#include "esp_bt_main.h"
#include "esp_bt_defs.h"
#include "esp_ibeacon_api.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"

#include "protocol_examples_common.h"
#include "esp_event.h"
#include "mbedtls/platform.h"
#include "mbedtls/net_sockets.h"
#include "mbedtls/esp_debug.h"
#include "mbedtls/ssl.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/error.h"
#include "mbedtls/certs.h"
#include <mbedtls/base64.h>
#include <sys/param.h>


#include <time.h>
#include "driver/gpio.h"

// #define femi_light
#define femi_pod


#define ESP_UUID_test {0xE2, 0xC5, 0x6D, 0xB5, 0xDF, 0xFB, 0x48, 0xD2, 0xB0, 0x60, 0xD0, 0xF5, 0xA7, 0x10, 0x96, 0xE0}

static const char* DEMO_TAG = "IBEACON_DEMO";
static const char* DEBUG_TAG = "DEBUG_PURPOSE";
extern esp_ble_ibeacon_vendor_t vendor_config;
static time_t now;
static bool volatile init = false;
static volatile bool intervention_device_state = false;
static int eventLogger = 0;
static int cumulative_count;
uint32_t test_time = 60;
#define duration 1800 // 30 minutes 
#define BEACON_TIMEOUT 5
static uint8_t restart_count = 0;
bool restart_scanning = false;
#define REPORT_PERIOD_IN_HOURS 12
#define RESTART_TIMEOUT 1
uint32_t elapsed_time_ref;

///Declare static functions
static void esp_gap_cb(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param);

static void changing_device_state()
{
    if(intervention_device_state)
    {
        gpio_set_level(GPIO_NUM_15, 0); //Set H1 high
        //gpio_set_level(GPIO_NUM_2, 0); //Set H2 low
        gpio_set_level(GPIO_NUM_4, 1); //Set H3 low
        gpio_set_level(GPIO_NUM_16, 1);
    }
    else{
        gpio_set_level(GPIO_NUM_15, 1); //Set H1 high
        //gpio_set_level(GPIO_NUM_2, 0); //Set H2 low
        gpio_set_level(GPIO_NUM_4, 0); //Set H3 low
        gpio_set_level(GPIO_NUM_16, 0);
    }
}

#define MAX_NEARBY_DEVICES 256
typedef struct
{
    uint8_t uuid_name[16];
    time_t time_ref;
}nearby_devices_t;

nearby_devices_t nearby_devices[MAX_NEARBY_DEVICES];

int nearby_devices_size = 0;
int timer_ptr = 0;

int find_nearby_device(uint8_t *uuid_test)
{
    for(int i=0; i < nearby_devices_size; i++ )
    {
        if(!memcmp(nearby_devices[i].uuid_name, uuid_test,16))
        {
            return i;
        }
    }

    return -1;
}

int add_nearby_device(uint8_t *uuid_add)
{
    int ptr = nearby_devices_size;
    memcpy(nearby_devices[nearby_devices_size++].uuid_name,uuid_add,16);

    if(nearby_devices_size >= MAX_NEARBY_DEVICES)
    {
        nearby_devices_size--;
        return -1;
    }
    return ptr;
}

int remove_nearby_device( uint8_t* uuid_remove)
{
    int ptr = find_nearby_device(uuid_remove);
    if(ptr == -1)
    {
        return -1;
    }
    for(int i = ptr; i < (nearby_devices_size -1); i++)
    {
        nearby_devices[i] = nearby_devices[i +1];
    }
    nearby_devices_size--;

    return nearby_devices_size;
}

void nearby_timer_func()
{
    // ESP_LOGI(DEBUG_TAG, "time(now) [%li]",time(now));
    // ESP_LOGI(DEBUG_TAG, "nearby_devices[timer_ptr].time_ref [%li]",nearby_devices[timer_ptr].time_ref);

    if(nearby_devices_size)
    {
        if((time(now) - nearby_devices[timer_ptr].time_ref) >= (time_t)BEACON_TIMEOUT)
        {
            esp_log_buffer_hex("IBEACON_DEMO: lost UUID:", nearby_devices[timer_ptr].uuid_name, ESP_UUID_LEN_128);
            remove_nearby_device(nearby_devices[timer_ptr].uuid_name);
        }
        if(++timer_ptr >= nearby_devices_size)
        {
            timer_ptr = 0;
        }
    }
}

esp_ble_ibeacon_vendor_t testVar = {
    .proximity_uuid = ESP_UUID_test,
    .major = ENDIAN_CHANGE_U16(ESP_MAJOR), //Major=ESP_MAJOR
    .minor = ENDIAN_CHANGE_U16(ESP_MINOR), //Minor=ESP_MINOR
    .measured_power = 0xC5
};

//------------------------------------------------ smtp_client ---------------------------------------------

#define CONFIG_SMTP_SERVER "smtp.gmail.com"
#define CONFIG_SMTP_PORT_NUMBER "587"
#define CONFIG_SMTP_SENDER_MAIL "femifunction2@gmail.com"
#define CONFIG_SMTP_SENDER_PASSWORD "SuperAmy"
#define CONFIG_SMTP_RECIPIENT_MAIL "femifunction2@gmail.com"

#define MAIL_SERVER         CONFIG_SMTP_SERVER
#define MAIL_PORT           CONFIG_SMTP_PORT_NUMBER
#define SENDER_MAIL         CONFIG_SMTP_SENDER_MAIL
#define SENDER_PASSWORD     CONFIG_SMTP_SENDER_PASSWORD
#define RECIPIENT_MAIL      CONFIG_SMTP_RECIPIENT_MAIL

#define SERVER_USES_STARTSSL 1

static const char *TAG = "smtp_example";

#define TASK_STACK_SIZE     (8 * 1024)
#define BUF_SIZE            512

uint8_t instances_count = 0;

#define VALIDATE_MBEDTLS_RETURN(ret, min_valid_ret, max_valid_ret, goto_label)  \
    do {                                                                        \
        if (ret < min_valid_ret || ret > max_valid_ret) {                       \
            goto goto_label;                                                    \
        }                                                                       \
    } while (0)                                                                 \

/**
 * Root cert for smtp.googlemail.com, taken from server_root_cert.pem
 *
 * The PEM file was extracted from the output of this command:
 * openssl s_client -showcerts -connect smtp.googlemail.com:587 -starttls smtp
 *
 * The CA root cert is the last cert given in the chain of certs.
 *
 * To embed it in the app binary, the PEM file is named
 * in the component.mk COMPONENT_EMBED_TXTFILES variable.
 */

extern const uint8_t server_root_cert_pem_start[] asm("_binary_server_root_cert_pem_start");
extern const uint8_t server_root_cert_pem_end[]   asm("_binary_server_root_cert_pem_end");

extern const uint8_t esp_logo_png_start[] asm("_binary_esp_logo_png_start");
extern const uint8_t esp_logo_png_end[]   asm("_binary_esp_logo_png_end");

static int write_and_get_response(mbedtls_net_context *sock_fd, unsigned char *buf, size_t len)
{
    int ret;
    const size_t DATA_SIZE = 128;
    unsigned char data[DATA_SIZE];
    char code[4];
    size_t i, idx = 0;

    if (len) {
        ESP_LOGD(TAG, "%s", buf);
    }

    if (len && (ret = mbedtls_net_send(sock_fd, buf, len)) <= 0) {
        ESP_LOGE(TAG, "mbedtls_net_send failed with error -0x%x", -ret);
        return ret;
    }

    do {
        len = DATA_SIZE - 1;
        ret = mbedtls_net_recv(sock_fd, data, len);

        if (ret <= 0) {
            ESP_LOGE(TAG, "mbedtls_net_recv failed with error -0x%x", -ret);
            goto exit;
        }

        data[len] = '\0';
        printf("\n%s", data);
        len = ret;
        for (i = 0; i < len; i++) {
            if (data[i] != '\n') {
                if (idx < 4) {
                    code[idx++] = data[i];
                }
                continue;
            }

            if (idx == 4 && code[0] >= '0' && code[0] <= '9' && code[3] == ' ') {
                code[3] = '\0';
                ret = atoi(code);
                goto exit;
            }

            idx = 0;
        }
    } while (1);

exit:
    return ret;
}

static int write_ssl_and_get_response(mbedtls_ssl_context *ssl, unsigned char *buf, size_t len)
{
    int ret;
    const size_t DATA_SIZE = 128;
    unsigned char data[DATA_SIZE];
    char code[4];
    size_t i, idx = 0;

    if (len) {
        ESP_LOGD(TAG, "%s", buf);
    }

    while (len && (ret = mbedtls_ssl_write(ssl, buf, len)) <= 0) {
        if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
            ESP_LOGE(TAG, "mbedtls_ssl_write failed with error -0x%x", -ret);
            goto exit;
        }
    }

    do {
        len = DATA_SIZE - 1;
        ret = mbedtls_ssl_read(ssl, data, len);

        if (ret == MBEDTLS_ERR_SSL_WANT_READ || ret == MBEDTLS_ERR_SSL_WANT_WRITE) {
            continue;
        }

        if (ret <= 0) {
            ESP_LOGE(TAG, "mbedtls_ssl_read failed with error -0x%x", -ret);
            goto exit;
        }

        ESP_LOGD(TAG, "%s", data);

        len = ret;
        for (i = 0; i < len; i++) {
            if (data[i] != '\n') {
                if (idx < 4) {
                    code[idx++] = data[i];
                }
                continue;
            }

            if (idx == 4 && code[0] >= '0' && code[0] <= '9' && code[3] == ' ') {
                code[3] = '\0';
                ret = atoi(code);
                goto exit;
            }

            idx = 0;
        }
    } while (1);

exit:
    return ret;
}

static int write_ssl_data(mbedtls_ssl_context *ssl, unsigned char *buf, size_t len)
{
    int ret;

    if (len) {
        ESP_LOGD(TAG, "%s", buf);
    }

    while (len && (ret = mbedtls_ssl_write(ssl, buf, len)) <= 0) {
        if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
            ESP_LOGE(TAG, "mbedtls_ssl_write failed with error -0x%x", -ret);
            return ret;
        }
    }

    return 0;
}

static int perform_tls_handshake(mbedtls_ssl_context *ssl)
{
    int ret = -1;
    uint32_t flags;
    char *buf = NULL;
    buf = (char *) calloc(1, BUF_SIZE);
    if (buf == NULL) {
        ESP_LOGE(TAG, "calloc failed for size %d", BUF_SIZE);
        goto exit;
    }

    ESP_LOGI(TAG, "Performing the SSL/TLS handshake...");

    fflush(stdout);
    while ((ret = mbedtls_ssl_handshake(ssl)) != 0) {
        if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
            ESP_LOGE(TAG, "mbedtls_ssl_handshake returned -0x%x", -ret);
            goto exit;
        }
    }

    ESP_LOGI(TAG, "Verifying peer X.509 certificate...");

    if ((flags = mbedtls_ssl_get_verify_result(ssl)) != 0) {
        /* In real life, we probably want to close connection if ret != 0 */
        ESP_LOGW(TAG, "Failed to verify peer certificate!");
        mbedtls_x509_crt_verify_info(buf, BUF_SIZE, "  ! ", flags);
        ESP_LOGW(TAG, "verification info: %s", buf);
    } else {
        ESP_LOGI(TAG, "Certificate verified.");
    }

    ESP_LOGI(TAG, "Cipher suite is %s", mbedtls_ssl_get_ciphersuite(ssl));
    ret = 0; /* No error */

exit:
    if (buf) {
        free(buf);
    }
    return ret;
}

static void smtp_client_task(void *pvParameters)
{
    char *buf = NULL;
    unsigned char base64_buffer[128];
    int ret, len;
    size_t base64_len;

    mbedtls_entropy_context entropy;
    mbedtls_ctr_drbg_context ctr_drbg;
    mbedtls_ssl_context ssl;
    mbedtls_x509_crt cacert;
    mbedtls_ssl_config conf;
    mbedtls_net_context server_fd;

    mbedtls_ssl_init(&ssl);
    mbedtls_x509_crt_init(&cacert);
    mbedtls_ctr_drbg_init(&ctr_drbg);
    ESP_LOGI(TAG, "Seeding the random number generator");

    mbedtls_ssl_config_init(&conf);

    mbedtls_entropy_init(&entropy);
    if ((ret = mbedtls_ctr_drbg_seed(&ctr_drbg, mbedtls_entropy_func, &entropy,
                                     NULL, 0)) != 0) {
        ESP_LOGE(TAG, "mbedtls_ctr_drbg_seed returned -0x%x", -ret);
        goto exit;
    }

    ESP_LOGI(TAG, "Loading the CA root certificate...");

    ret = mbedtls_x509_crt_parse(&cacert, server_root_cert_pem_start,
                                 server_root_cert_pem_end - server_root_cert_pem_start);

    if (ret < 0) {
        ESP_LOGE(TAG, "mbedtls_x509_crt_parse returned -0x%x", -ret);
        goto exit;
    }

    ESP_LOGI(TAG, "Setting hostname for TLS session...");

    /* Hostname set here should match CN in server certificate */
    if ((ret = mbedtls_ssl_set_hostname(&ssl, MAIL_SERVER)) != 0) {
        ESP_LOGE(TAG, "mbedtls_ssl_set_hostname returned -0x%x", -ret);
        goto exit;
    }

    ESP_LOGI(TAG, "Setting up the SSL/TLS structure...");

    if ((ret = mbedtls_ssl_config_defaults(&conf,
                                           MBEDTLS_SSL_IS_CLIENT,
                                           MBEDTLS_SSL_TRANSPORT_STREAM,
                                           MBEDTLS_SSL_PRESET_DEFAULT)) != 0) {
        ESP_LOGE(TAG, "mbedtls_ssl_config_defaults returned -0x%x", -ret);
        goto exit;
    }

    mbedtls_ssl_conf_authmode(&conf, MBEDTLS_SSL_VERIFY_REQUIRED);
    mbedtls_ssl_conf_ca_chain(&conf, &cacert, NULL);
    mbedtls_ssl_conf_rng(&conf, mbedtls_ctr_drbg_random, &ctr_drbg);
#ifdef CONFIG_MBEDTLS_DEBUG
    mbedtls_esp_enable_debug_log(&conf, 4);
#endif

    if ((ret = mbedtls_ssl_setup(&ssl, &conf)) != 0) {
        ESP_LOGE(TAG, "mbedtls_ssl_setup returned -0x%x", -ret);
        goto exit;
    }

    mbedtls_net_init(&server_fd);

    ESP_LOGI(TAG, "Connecting to %s:%s...", MAIL_SERVER, MAIL_PORT);

    if ((ret = mbedtls_net_connect(&server_fd, MAIL_SERVER,
                                   MAIL_PORT, MBEDTLS_NET_PROTO_TCP)) != 0) {
        ESP_LOGE(TAG, "mbedtls_net_connect returned -0x%x", -ret);
        goto exit;
    }

    ESP_LOGI(TAG, "Connected.");

    mbedtls_ssl_set_bio(&ssl, &server_fd, mbedtls_net_send, mbedtls_net_recv, NULL);

    buf = (char *) calloc(1, BUF_SIZE);
    if (buf == NULL) {
        ESP_LOGE(TAG, "calloc failed for size %d", BUF_SIZE);
        goto exit;
    }
#if SERVER_USES_STARTSSL
    /* Get response */
    ret = write_and_get_response(&server_fd, (unsigned char *) buf, 0);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);

    ESP_LOGI(TAG, "Writing EHLO to server...");
    len = snprintf((char *) buf, BUF_SIZE, "EHLO %s\r\n", "ESP3zz2");
    ret = write_and_get_response(&server_fd, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);

    ESP_LOGI(TAG, "Writing STARTTLS to server...");
    len = snprintf((char *) buf, BUF_SIZE, "STARTTLS\r\n");
    ret = write_and_get_response(&server_fd, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);

    ret = perform_tls_handshake(&ssl);
    if (ret != 0) {
        goto exit;
    }

#else /* SERVER_USES_STARTSSL */
    ret = perform_tls_handshake(&ssl);
    if (ret != 0) {
        goto exit;
    }

    /* Get response */
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, 0);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);
    ESP_LOGI(TAG, "Writing EHLO to server...");

    len = snprintf((char *) buf, BUF_SIZE, "EHLO %s\r\n", "ESP32");
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);

#endif /* SERVER_USES_STARTSSL */

    /* Authentication */
    ESP_LOGI(TAG, "Authentication...");

    ESP_LOGI(TAG, "Write AUTH LOGIN");
    len = snprintf( (char *) buf, BUF_SIZE, "AUTH LOGIN\r\n" );
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 399, exit);

    ESP_LOGI(TAG, "Write USER NAME");
    ret = mbedtls_base64_encode((unsigned char *) base64_buffer, sizeof(base64_buffer),
                                &base64_len, (unsigned char *) SENDER_MAIL, strlen(SENDER_MAIL));
    if (ret != 0) {
        ESP_LOGE(TAG, "Error in mbedtls encode! ret = -0x%x", -ret);
        goto exit;
    }
    len = snprintf((char *) buf, BUF_SIZE, "%s\r\n", base64_buffer);
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 300, 399, exit);

    ESP_LOGI(TAG, "Write PASSWORD");
    ret = mbedtls_base64_encode((unsigned char *) base64_buffer, sizeof(base64_buffer),
                                &base64_len, (unsigned char *) SENDER_PASSWORD, strlen(SENDER_PASSWORD));
    if (ret != 0) {
        ESP_LOGE(TAG, "Error in mbedtls encode! ret = -0x%x", -ret);
        goto exit;
    }
    len = snprintf((char *) buf, BUF_SIZE, "%s\r\n", base64_buffer);
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 399, exit);

    /* Compose email */
    ESP_LOGI(TAG, "Write MAIL FROM");
    len = snprintf((char *) buf, BUF_SIZE, "MAIL FROM:<%s>\r\n", SENDER_MAIL);
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);

    ESP_LOGI(TAG, "Write RCPT");
    len = snprintf((char *) buf, BUF_SIZE, "RCPT TO:<%s>\r\n", RECIPIENT_MAIL);
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);

    ESP_LOGI(TAG, "Write DATA");
    len = snprintf((char *) buf, BUF_SIZE, "DATA\r\n");
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 300, 399, exit);

    ESP_LOGI(TAG, "Write Content");
    /* We do not take action if message sending is partly failed. */
    len = snprintf((char *) buf, BUF_SIZE,
                   "From: %s\r\nSubject: Interaction Count\r\n"
                   "To: %s\r\n"
                   "MIME-Version: 1.0 (mime-construct 1.9)\n",
                   "Femi Client", RECIPIENT_MAIL);

    /**
     * Note: We are not validating return for some ssl_writes.
     * If by chance, it's failed; at worst email will be incomplete!
     */
    ret = write_ssl_data(&ssl, (unsigned char *) buf, len);

    /* Multipart boundary */
    len = snprintf((char *) buf, BUF_SIZE,
                   "Content-Type: multipart/mixed;boundary=XYZabcd1234\n"
                   "--XYZabcd1234\n");
    ret = write_ssl_data(&ssl, (unsigned char *) buf, len);

    /* Text */
    len = snprintf((char *) buf, BUF_SIZE,
                   "Content-Type: text/plain\n"
                   "I am a POD device"
                   "This is a simple test mail from the FEMI SMTP client example Containing the Interaction count.\r\n"
                   "The Interaction count for the last 12 hours: [%d]\n\r"
                   "Cumulative interaction count: [%d]\n\r"
                   "\r\n"
                   "Enjoy!\n\n--XYZabcd1234\n", eventLogger, cumulative_count);
    ret = write_ssl_data(&ssl, (unsigned char *) buf, len);

    len = snprintf((char *) buf, BUF_SIZE, "\n--XYZabcd1234\n");
    ret = write_ssl_data(&ssl, (unsigned char *) buf, len);

    len = snprintf((char *) buf, BUF_SIZE, "\r\n.\r\n");
    ret = write_ssl_and_get_response(&ssl, (unsigned char *) buf, len);
    VALIDATE_MBEDTLS_RETURN(ret, 200, 299, exit);
    ESP_LOGI(TAG, "Email sent!");

    /* Close connection */
    mbedtls_ssl_close_notify(&ssl);
    ret = 0; /* No errors */

exit:
    mbedtls_ssl_session_reset(&ssl);
    mbedtls_net_free(&server_fd);

    if (ret != 0) {
        mbedtls_strerror(ret, buf, 100);
        ESP_LOGE(TAG, "Last error was: -0x%x - %s", -ret, buf);
    }

    putchar('\n'); /* Just a new line */
    if (buf) {
        free(buf);
    }
    restart_scanning = true;
    vTaskDelete(NULL);
    return;
}


//------------------------------------------------ end of smpt_client --------------------------------------



#if (IBEACON_MODE == IBEACON_RECEIVER)
static esp_ble_scan_params_t ble_scan_params = {
    .scan_type              = BLE_SCAN_TYPE_ACTIVE,
    .own_addr_type          = BLE_ADDR_TYPE_PUBLIC,
    .scan_filter_policy     = BLE_SCAN_FILTER_ALLOW_ONLY_WLST,
    .scan_interval          = 0x50,
    .scan_window            = 0x30,
    .scan_duplicate         = BLE_SCAN_DUPLICATE_MAX
};

#elif (IBEACON_MODE == IBEACON_SENDER)
static esp_ble_adv_params_t ble_adv_params = {
    .adv_int_min        = 0x20,
    .adv_int_max        = 0x40,
    .adv_type           = ADV_TYPE_NONCONN_IND,
    .own_addr_type      = BLE_ADDR_TYPE_PUBLIC,
    .channel_map        = ADV_CHNL_ALL,
    .adv_filter_policy = ADV_FILTER_ALLOW_SCAN_ANY_CON_ANY,
};
#endif


static void esp_gap_cb(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param)
{
    esp_err_t err;
    nearby_timer_func();
    switch (event) {
    case ESP_GAP_BLE_ADV_DATA_RAW_SET_COMPLETE_EVT:{ //1
#if (IBEACON_MODE == IBEACON_SENDER)
        esp_ble_gap_start_advertising(&ble_adv_params);
#endif
        break;
    }
    case ESP_GAP_BLE_SCAN_PARAM_SET_COMPLETE_EVT: { //2
#if (IBEACON_MODE == IBEACON_RECEIVER)
        //the unit of the duration is second, 0 means scan permanently
        esp_ble_gap_start_scanning(duration);

#endif
        break;
    }
    case ESP_GAP_BLE_SCAN_START_COMPLETE_EVT: //3
    ESP_LOGI(DEMO_TAG, "ESP_GAP_BLE_SCAN_START_COMPLETE_EVT");
        //scan start complete event to indicate scan start successfully or failed
        if ((err = param->scan_start_cmpl.status) != ESP_BT_STATUS_SUCCESS) {
            ESP_LOGE(DEMO_TAG, "Scan start failed: %s", esp_err_to_name(err));
        }
        else
        {
            ESP_LOGI(DEMO_TAG, "esp err to name: %s", esp_err_to_name(err));
        }
        break;
    case ESP_GAP_BLE_ADV_START_COMPLETE_EVT: //4
    ESP_LOGI(DEMO_TAG, "ESP_GAP_BLE_ADV_START_COMPLETE_EVT");
        //adv start complete event to indicate adv start successfully or failed
        if ((err = param->adv_start_cmpl.status)                                               != ESP_BT_STATUS_SUCCESS) {
            ESP_LOGE(DEMO_TAG, "Adv start failed: %s", esp_err_to_name(err));
        }
        break;
    case ESP_GAP_BLE_SCAN_RESULT_EVT: { //5
        esp_ble_gap_cb_param_t *scan_result = (esp_ble_gap_cb_param_t *)param;
        // ESP_LOGI(DEMO_TAG, "ESP_GAP_BLE_SCAN_RESULT_EVT[%i]",ESP_GAP_BLE_SCAN_RESULT_EVT);
        // ESP_LOGI(DEMO_TAG, "scan_result->scan_rst.search_evt[%i]",scan_result->scan_rst.search_evt);
        // ESP_LOGI(DEBUG_TAG, "Scan restart: %i", restart_count);
        switch (scan_result->scan_rst.search_evt) {
        case ESP_GAP_SEARCH_INQ_RES_EVT:
            /* Search for BLE iBeacon Packet */
    #if 1
            if (esp_ble_is_ibeacon_packet(scan_result->scan_rst.ble_adv, scan_result->scan_rst.adv_data_len))
            {
                esp_ble_ibeacon_t *ibeacon_data = (esp_ble_ibeacon_t*)(scan_result->scan_rst.ble_adv);
                ESP_LOGI(DEMO_TAG, "----------iBeacon Found----------");
                // esp_log_buffer_hex("IBEACON_DEMO: Device address:", scan_result->scan_rst.bda, ESP_BD_ADDR_LEN );
                // esp_log_buffer_hex("IBEACON_DEMO: Proximity UUID:", ibeacon_data->ibeacon_vendor.proximity_uuid, ESP_UUID_LEN_128);
                // esp_log_buffer_hex("Femi: Proximity UUID:", testVar.proximity_uuid, ESP_UUID_LEN_128);


                if(!memcmp(testVar.proximity_uuid , ibeacon_data->ibeacon_vendor.proximity_uuid, 16) &&
                       scan_result->scan_rst.rssi > -78 )
                {
                    time(&now);
                    now = now * 1000;

                    if(!intervention_device_state)
                    {
                        intervention_device_state = true;
                        changing_device_state();
                        eventLogger++;
                        ESP_LOGI(DEMO_TAG, "Event Logger, %d", eventLogger);
                    }
                }

                else if(((time(0)*(time_t)1000) - now) > (time_t)2500) //2000 for pod, 2200 for light
                {
                    intervention_device_state = false;
                    changing_device_state();
                    // ESP_LOGI(DEMO_TAG, "---------- femi not Found----------");
                }
            }

            else if(intervention_device_state)
            {
                if(((time(0)*(time_t)1000) - now) > (time_t)2500)
                {
                        intervention_device_state = false;
                        changing_device_state();
                        //ESP_LOGI(GATTC_TAG, "Unknown Device");

                }
                // ESP_LOGI(DEMO_TAG, "----------femi Found----------");
            }
            else
            {
                esp_log_buffer_hex("beacon packet: ", scan_result->scan_rst.ble_adv, scan_result->scan_rst.adv_data_len);
                ESP_LOGI(DEBUG_TAG, "Unknown Device");
            }
 #else
             if (esp_ble_is_ibeacon_packet(scan_result->scan_rst.ble_adv, scan_result->scan_rst.adv_data_len))
            {
                int ptr;

                esp_ble_ibeacon_t *ibeacon_data = (esp_ble_ibeacon_t*)(scan_result->scan_rst.ble_adv);
                if((ptr =find_nearby_device(ibeacon_data->ibeacon_vendor.proximity_uuid)) == -1)
                {
                    ESP_LOGI(DEBUG_TAG, "NEW IBEACON FOUND");
                    esp_log_buffer_hex("IBEACON_DEMO: found Proximity UUID:", ibeacon_data->ibeacon_vendor.proximity_uuid, ESP_UUID_LEN_128);
                    int new_ptr = add_nearby_device(ibeacon_data->ibeacon_vendor.proximity_uuid);
                    nearby_devices[new_ptr].time_ref = time(now);
                    //ESP_LOGI(DEBUG_TAG, "new_ptr[%i]", new_ptr);
                }
                else
                {
                     nearby_devices[ptr].time_ref = time(now);
                }
            }


 #endif
            break;

        case ESP_GAP_SEARCH_INQ_CMPL_EVT:
                cumulative_count = eventLogger;

                if (time(now) - elapsed_time_ref >= (REPORT_PERIOD_IN_HOURS * 60 * 60))
                {
                   xTaskCreate(&smtp_client_task, "smtp_client_task", TASK_STACK_SIZE, NULL, 5, NULL);
                }
                             
        
                if(restart_scanning) // TODO need to figure this logic out a bit, does not make sense
                {
                    esp_ble_gap_start_scanning(duration);
                    restart_scanning = false;
                }
                else if(time(now) - elapsed_time_ref > RESTART_TIMEOUT)
                {
                    esp_ble_gap_start_scanning(duration);
                }
                
            break;

        default:
            break;
        }
        break;
    }

    case ESP_GAP_BLE_SCAN_STOP_COMPLETE_EVT: //6
        if ((err = param->scan_stop_cmpl.status) != ESP_BT_STATUS_SUCCESS){
            ESP_LOGE(DEMO_TAG, "Scan stop failed: %s", esp_err_to_name(err));
        }
        else {
            ESP_LOGI(DEMO_TAG, "Stop scan successfully");
        }
        break;

    case ESP_GAP_BLE_ADV_STOP_COMPLETE_EVT:
        if ((err = param->adv_stop_cmpl.status) != ESP_BT_STATUS_SUCCESS){
            ESP_LOGE(DEMO_TAG, "Adv stop failed: %s", esp_err_to_name(err));
        }
        else {
            ESP_LOGI(DEMO_TAG, "Stop adv successfully");
        }
        break;

    default:
        break;
    }
}


void ble_ibeacon_appRegister(void)
{
    esp_err_t status;

    ESP_LOGI(DEMO_TAG, "register callback");

        //register the scan callback function to the gap module
    if ((status = esp_ble_gap_register_callback(esp_gap_cb)) != ESP_OK) {
        ESP_LOGE(DEMO_TAG, "gap register error: %s", esp_err_to_name(status));
        return;
    }

}

void ble_ibeacon_init(void)
{
    esp_bluedroid_init();
    esp_bluedroid_enable();
    ble_ibeacon_appRegister();
}

void app_main(void)
{
    if(!init)
    {
        gpio_config_t gp;
        gp.intr_type = GPIO_INTR_DISABLE;
        gp.mode = GPIO_MODE_OUTPUT;
        gp.pin_bit_mask = GPIO_SEL_15 | GPIO_SEL_2 | GPIO_SEL_4 | GPIO_SEL_16;
        gpio_config(&gp);

        gpio_set_level(GPIO_NUM_15, 1); //Set H1 high
        gpio_set_level(GPIO_NUM_2, 0); //Set H2 low
        gpio_set_level(GPIO_NUM_4, 0); //Set H3 low
        gpio_set_level(GPIO_NUM_16, 0);

        elapsed_time_ref = time(now);

        init = true;
    }

    ESP_ERROR_CHECK(nvs_flash_init());
    ESP_ERROR_CHECK(esp_bt_controller_mem_release(ESP_BT_MODE_CLASSIC_BT));
    esp_bt_controller_config_t bt_cfg = BT_CONTROLLER_INIT_CONFIG_DEFAULT();
    esp_bt_controller_init(&bt_cfg);
    esp_bt_controller_enable(ESP_BT_MODE_BLE);

    ble_ibeacon_init();

    ESP_ERROR_CHECK(esp_event_loop_create_default());

    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(example_connect());


    /* set scan parameters */
#if (IBEACON_MODE == IBEACON_RECEIVER)

    esp_bd_addr_t testAdr= {0xF3 , 0x2C ,0x63 , 0x4A, 0xED, 0xEF};

    if(esp_ble_gap_update_whitelist(ESP_BLE_WHITELIST_ADD,testAdr,BLE_WL_ADDR_TYPE_PUBLIC) ==ESP_OK)
    {
        ESP_LOGI(DEBUG_TAG,"ADDED FEMI TO WHITELIST");
    }
    else
    {
        ESP_LOGI(DEBUG_TAG, "error adding to whitelist");
    }
    esp_ble_gap_set_scan_params(&ble_scan_params);

#elif (IBEACON_MODE == IBEACON_SENDER)
    esp_ble_ibeacon_t ibeacon_adv_data;
    esp_err_t status = esp_ble_config_ibeacon_data (&vendor_config, &ibeacon_adv_data);
    if (status == ESP_OK){
        esp_ble_gap_config_adv_data_raw((uint8_t*)&ibeacon_adv_data, sizeof(ibeacon_adv_data));
    }
    else {
        ESP_LOGE(DEMO_TAG, "Config iBeacon data failed: %s\n", esp_err_to_name(status));
    }
#endif

}
